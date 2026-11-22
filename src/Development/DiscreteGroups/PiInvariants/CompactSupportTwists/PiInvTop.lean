module

public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvOf
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClos

@[expose] public section

namespace DiscreteGroups.T1.G

theorem piInv : PositivityTheory.Rg.BcB.Desc.PiInv := piInv_of piClosureInv

end DiscreteGroups.T1.G
