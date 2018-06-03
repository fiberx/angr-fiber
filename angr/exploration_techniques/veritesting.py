from . import ExplorationTechnique

class Veritesting(ExplorationTechnique):
    """
    Enable veritesting. This technique, described in a paper[1] from CMU, attempts to address the problem of state
    explosions in loops by performing smart merging.

    [1] https://users.ece.cmu.edu/~aavgerin/papers/veritesting-icse-2014.pdf
    """
    def __init__(self, **options):
        super(Veritesting, self).__init__()
        self.options = options

    #HZ: We need to do some modifications here mainly because we want to combine 'veritesting' and 'explorer'.
    #(1) 'explorer' uses 'found' and 'avoid' stashes, which also need to be returned here.
    #(2) 'successful' stash contains overbound (the 'boundary' of veritesting is provided by user) and overlooping states, we
    #don't want to continue with these states anyway, so DON'T move them to 'active' stash.
    def step_state(self, state, **kwargs):
        vt = self.project.analyses.Veritesting(state, **self.options)
        if vt.result and vt.final_manager:
            simgr = vt.final_manager
            simgr.stash(from_stash='deviated', to_stash='active')
            #simgr.stash(from_stash='successful', to_stash='active')

            return {
                    'active': simgr.active,
                    'unconstrained': simgr.stashes.get('unconstrained', []),
                    'unsat': simgr.stashes.get('unsat', []),
                    'found': simgr.stashes.get('found', []),
                    'avoid': simgr.stashes.get('avoid', []),
                    }

        return None
