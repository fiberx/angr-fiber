#HZ: We implement a new addr concretization strategy here, it follows some principles:
#(1) If available range is unlimited, then use 'addr bucket' mechanism to pick one result, hopefully this will avoid conflicts.
#(2) If available range is less than 'limit', return 'limit' results.
#(3) If it's neither 1 or 2, then return one random result.

#HZ: Why we need this?

#[NOTE] A fundamental problem of Angr's symbolic address concretization is the potential 'repeat' (or collision)
#Consider following instruction sequence:
# 1 ldr x1,[x0+0x20]
# 2 ldr x2,[x1,0x268]
#In 1, x0 is an unconstrained symbolic variable, so when we want to concretize 'x0+0x20', there are infinite answers but
#'range' strategy only support a limited number of answers, so we use 'any' strategy to pick just one possible answer.
#After concretization of 'x0+0x20', to maintain consistency a constrains will be added to current state that 'from now on
#x0 must hold this previously picked answer, it will be fixed'. Then x1, the memory content, is also an unlimited symbolic
#variable, thus in 2 'x1+0x268' also needs to be concretized, as the same for 1, here we also have infinite choices and
#finally we need to just pick one answer. Now comes the problem, the answer we pick may make 'x1+0x268' == 'x0+0x20'...
#In theory, this can be true in practice, but recall that we want the formula like x2 = [[x0+0x20]+0x268], while if this
#equation is true, we will end up wit x2 = [[x0+0x20]]...
#[SOLUTION]
#(1) Record every 'address --> addr_expr' in a dict
#(2) If we find two different addr_expr are concretized to a same addr but at least one addr_expr has other choices, we will try
#to concretize it to another address.

#Why addr_bucket can help?

#For many collisions we cannot resolve them due to the fact that there already exists certain constraints for symbolic values.
#E.g. 
#1 ldr x1,[x0+0x20]
#2 ldr x2,[x1,0x268]
#3 ldr x3,[x1,0x368]
#It's possible that in 2 we don't have collision but then in 3 we have 'x1 + 0x368' == 'x0 + 0x20', however, 'x1' is no longer
#unlimited in 3, in fact 2 has already put a strict constraint in 'x1' when doing its concretization.
#[PLAY A POSSIBILITY GAME]
#We cannot foreseen possible collision in the future, but we can introduce some randomness here when picking value for an unlimited symbol.
#Thus hopefully we will eventually get a collision-free run when we running it for multiple times.
from . import SimConcretizationStrategy
import random,re
import claripy

class SimConcretizationStrategyHZ(SimConcretizationStrategy):

    def __init__(self, limit=3, **kwargs): #pylint:disable=redefined-builtin
        super(SimConcretizationStrategyHZ, self).__init__(**kwargs)
        self._limit = limit
        self._addr_buck_step = 0x2000
        self._addr_buck = random.randint(1,100) * self._addr_buck_step
        self._addr_expr_map = {}
        self._resolve_number = 16
        self.collision = False

    def _is_unlimited_aarch64(self,mn,mx):
        return mn == 0 and mx == 0xffffffffffffffff

    def _concretize(self, memory, addr):
        if memory.state.arch.name not in ('AARCH64'):
            print '[SimConcretizationStrategyHZ] No support for arch: ' + memory.state.arch.name
            return None
        mn,mx = self._range(memory, addr)
        #TODO: Change this if you want to support more archs.
        if self._is_unlimited_aarch64(mn,mx):
            i = self._addr_buck
            while self._is_addr_collision(i,addr):
                i = i + 8
            self._addr_buck = i + self._addr_buck_step
            return [i]
        elif mn == mx:
            #This is an optimization, no other choices here and we don't need to call eval again.
            if self._is_addr_collision(mn,addr):
                #It *may* (our current cmp_addr_expr cannot capture some semantic equivalent formulas) be a collision, but anyway we have no choices.
                print '[Addr Collision] %s @ %x, with %s' % (str(addr),mn,str(self._addr_expr_map[mn]))
                self.collision = True
            return [mn]
        elif mx - mn <= self._limit:
            cands =  self._eval(memory, addr, self._limit)
            filt = filter(lambda x:not self._is_addr_collision(x,addr),cands)
            if not filt:
                #All the candidates have a collision, in this case we return a random *one*
                res =  random.choice(cands)
                print '[Addr Collision] %s @ %x, with %s' % (str(addr),res,str(self._addr_expr_map[res]))
                self.collision = True
                return [res]
            else:
                return filt
        else:
            #Possible choices are not unlimited, but also more than '_limit'.. 
            #To avoid collision at best effort, we first eval *_resolve_number* candidates and choose a non-conflict one.
            cands = self._eval(memory, addr, self._resolve_number)
            for cand in cands:
                if self._is_addr_collision(cand,addr):
                    continue
                return [cand]
            print '[Shit] Cannot find non-conflict solution with %d candidates' % self._resolve_number
            print '[Addr Collision] %s @ %x, with %s' % (str(addr),cand,str(self._addr_expr_map[cand]))
            self.collision = True
            return [cand]

    #Whether there is any collision regarding the concretization result.
    def _is_addr_collision(self,addr,expr,update=True):
        if addr in self._addr_expr_map:
            if self._cmp_addr_expr(expr,self._addr_expr_map[addr]):
                #Evaluate a same expr again, no confliction.
                return False
            else:
                return True
        else:
            #Haven't evaluated such a expr before.
            if update:
                self._addr_expr_map[addr] = expr
            return False

    #Compare two addr exprs to see whether they are the same, this is certainly not as complicated as comparison in actual matching phase,
    #instead we only do some very simple comparisons here. 
    #Return True if matched.
    def _cmp_addr_expr(self,e1,e2):
        #[NOTE] The problem to note here is addr collision should only happen inside one state/path because different
        #states have separate memory spaces. Besides, one state should have only one symbol for a same memory address,
        #thus, if we see two mem symbols have same addr but different 'numeric suffix', they are possibly created by two states. 
        _to_str = lambda x:self._mask_num_suffix(str(x))
        if _to_str(e1) == _to_str(e2):
            return True
        elif e1.op == e2.op and e1.op in claripy.operations.commutative_operations and len(e1.args) == len(e2.args):
            #We want to capture a simple case here: X +/* Y == Y +/* X
            sa1 = set([_to_str(a) for a in e1.args])
            sa2 = set([_to_str(a) for a in e2.args])
            if sa1 == sa2:
                return True
        return False

    def _mask_num_suffix(self,s):
        regex = '(reg|mem)_[\da-f]+_[\d]+_[\d]+'
        def _mask(s):
            if s is not str:
                s = s.group(0)
            tokens = s.split('_')
            if len(tokens) <> 4:
                return s
            tokens.pop(-2)
            return '_'.join(tokens)
        return re.sub(regex,_mask,s)
