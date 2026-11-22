module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

@[expose] public section

namespace LateralTheory.CohomologicalPurity

theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
