import logging
from copy import copy

from . import Analysis, register_analysis
from networkx import DiGraph

l = logging.getLogger("angr.analyses.dfg")

class DFG(Analysis):
    #HZ: Here we do some modifications to let this support analysis for several specified basic blocks, making it more flexible.
    #HZ: besides, we add parameter 'opt_level' to enable us to control the optimization level in asm-->vex process.
    def __init__(self, cfg=None, annocfg=None, nodes=None, opt_level=None):
        """
        Build a Data Flow Grah (DFG) for every basic block of a CFG

        The DFGs are available in the dict self.dfgs where the key
        is a basic block addr and the value a DFG.

        :param cfg: A CFG used to get all the basic blocks
        :param annocfg: An AnnotatedCFG built from a backward slice used to only build the DFG on the whitelisted statements
        """
        if cfg is None and nodes is None:
            self._cfg = self.project.analyses.CFGAccurate()
        else:
            self._cfg = cfg
        self._annocfg = annocfg
        #HZ: new parameters
        self._nodes = nodes
        self._opt_level = opt_level

        self.dfgs = self._construct()

    def _need_to_ignore(self, addr, stmt, stmt_idx):
        if self._annocfg is not None:
            whitelist = self._annocfg.get_whitelisted_statements(addr)
            if whitelist is False or (whitelist is not None and stmt_idx not in whitelist):
                return True
        #HZ: I'm not sure why we should exclude 'Ist_Exit' here
        #if stmt.tag == 'Ist_IMark' or stmt.tag == 'Ist_AbiHint' or stmt.tag == 'Ist_Exit':
        if stmt.tag == 'Ist_IMark' or stmt.tag == 'Ist_AbiHint':
            return True
        elif stmt.tag == 'Ist_Put':
            arch = self.project.arch
            if stmt.offset in arch.register_names:
                if stmt.offset == arch.ip_offset:
                    return True
        return False

    def _construct(self):
        """
        We want to build the type of DFG that's used in "Automated Ident. of Crypto
        Primitives in Binary Code with Data Flow Graph Isomorphisms." Unlike that
        paper, however, we're building it on Vex IR instead of assembly instructions.
        """
        cfg = self._cfg
        p = self.project
        dfgs = {}
        l.debug("Building Vex DFG...")

        #HZ: to support analysis for a list of custom-specified basic blocks.
        node_list = self._nodes if self._nodes is not None else cfg.nodes()

        for node in node_list:
            #HZ: the passed-in 'node' can simply be an address  
            node_addr = node.addr if hasattr(node,'addr') else node
            node_size = node.size if hasattr(node,'size') else None
            try:
                #HZ: if we pass some nodes in DiGraph, then they may not have the 'simprocedure_name' field.
                if not hasattr(node,'simprocedure_name') or node.simprocedure_name == None:
                    irsb = p.factory.block(node_addr,opt_level=self._opt_level,size=node_size).vex
                else:
                    l.debug("Cannot process SimProcedures, ignoring %s" % node.simprocedure_name)
                    continue
            except Exception as e:
                l.debug(e)
                continue
            tmpsnodes = {}
            storesnodes = {}
            putsnodes = {}
            statements = irsb.statements
            dfg = DiGraph()
            #HZ: to record the instruction address.
            ins_addr = 0x0
            #irsb.pp()

            for stmt_idx, stmt in enumerate(statements):
                #HZ: we need to record the address of current instruction.
                if stmt.tag == 'Ist_IMark':
                    ins_addr = stmt.addr

                # We want to skip over certain types, such as Imarks
                if self._need_to_ignore(node_addr, stmt, stmt_idx):
                    continue

                # break statement down into sub-expressions
                exprs = stmt.expressions
                #HZ: We need the address and id of each stmt in the node.
                stmt_node = Dfg_Node(ins_addr,stmt_idx,stmt)
                dfg.add_node(stmt_node)

                #print '%d %s %s' % (stmt_idx,str(stmt),stmt.tag)
                if stmt.tag == 'Ist_WrTmp':
                    tmpsnodes[stmt.tmp] = stmt_node
                    if exprs[0].tag == 'Iex_Binop':
                        if exprs[1].tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[1], stmt_node)
                        if exprs[2].tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[exprs[2].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[2], stmt_node)

                    elif exprs[0].tag == 'Iex_Unop':
                        dfg.remove_node(stmt_node)
                        if exprs[1].tag == 'Iex_RdTmp':
                            #HZ: Don't make this optimization, cause our focus is accurate dependency relationship.
                            #tmpsnodes[stmt.tmp] = copy(tmpsnodes[exprs[1].tmp])
                            #tmpsnodes[stmt.tmp].tmp = stmt.tmp
                            dfg.add_edge(tmpsnodes[exprs[1].tmp],stmt_node)
                        else:
                            #HZ: Don't make this optimization, cause our focus is accurate dependency relationship.
                            #tmpsnodes[stmt.tmp] = exprs[1]
                            dfg.add_edge(exprs[1],stmt_node)

                    elif exprs[0].tag == 'Iex_RdTmp':
                        #HZ: Don't make this optimization, cause our focus is accurate dependency relationship.
                        #tmpsnodes[stmt.tmp] = copy(tmpsnodes[exprs[0].tmp])
                        #tmpsnodes[stmt.tmp].tmp = stmt.tmp
                        dfg.add_edge(tmpsnodes[exprs[0].tmp],stmt_node)

                    elif exprs[0].tag == 'Iex_Get':
                        if putsnodes.has_key(exprs[0].offset):
                            dfg.add_edge(putsnodes[exprs[0].offset], stmt_node)
                        if len(exprs) > 1 and exprs[1].tag == "Iex_RdTmp":
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        elif len(exprs) > 1:
                            dfg.add_edge(exprs[1], stmt_node)

                    elif exprs[0].tag == 'Iex_Load':
                        if exprs[1].tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[1], stmt_node)

                    else:
                        # Take a guess by assuming exprs[0] is the op and any other expressions are args
                        for e in exprs[1:]:
                            if e.tag == 'Iex_RdTmp':
                                dfg.add_edge(tmpsnodes[e.tmp], stmt_node)
                            else:
                                dfg.add_edge(e, stmt_node)

                elif stmt.tag == 'Ist_Store':
                    if exprs[0].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)

                    elif exprs[0].tag == 'Iex_Const':
                        dfg.add_edge(exprs[0], stmt_node)

                    if exprs[1].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                    else:
                        dfg.add_edge(exprs[1], stmt_node)

                elif stmt.tag == 'Ist_Put':
                    if exprs[0].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)
                    elif exprs[0].tag == 'Iex_Const':
                        dfg.add_edge(exprs[0], stmt_node)
                    putsnodes[stmt.offset] = stmt_node

                elif stmt.tag == 'Ist_Exit':
                    if exprs[0].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)

                elif stmt.tag == 'Ist_Dirty':
                    tmpsnodes[stmt.tmp] = stmt_node
                elif stmt.tag == 'Ist_CAS':
                    tmpsnodes[stmt.oldLo] = stmt_node
                else:
                    #HZ: Added by us to capture another case.
                    if stmt.tag == 'Ist_LLSC':
                        #It's a load-linked (stmt.storedata is None) or store-conditional stmt, anyway, the target is a tmp (stmt.result)
                        tmpsnodes[stmt.result] = stmt_node
                    for e in stmt.expressions:
                        if e.tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[e.tmp], stmt_node)
                        else:
                            dfg.add_edge(e, stmt_node)

            r_nodes = []
            for vtx in dfg.nodes():
                if dfg.degree(vtx) == 0:
                    r_nodes += [vtx]
            dfg.remove_nodes_from(r_nodes)

            if dfg.size() > 0:
                dfgs[node_addr] = dfg
        return dfgs

#HZ:A class representing a node in a DFG, wrapping a stmt and providing extra information.
class Dfg_Node(object):
    def __init__(self,addr,idx,stmt):
        self.ins_addr = addr
        self.st_idx = idx
        self.stmt = stmt

    def __getattr__(self,attr):
        return getattr(self.stmt,attr)

    def __setattr__(self,attr,value):
        #if attr in self.__dict__.keys():
        if attr == 'stmt' or attr == 'ins_addr' or attr == 'st_idx':
            self.__dict__[attr] = value
        else:
            setattr(self.stmt,attr,value)
    
    def __str__(self):
        return hex(self.ins_addr) + ',' +str(self.st_idx) + ',' + str(self.stmt)
    
    def __setstate__(self, data):
        self.__dict__.update(data)

    def __getstate__(self):
        return self.__dict__

register_analysis(DFG, 'DFG')
