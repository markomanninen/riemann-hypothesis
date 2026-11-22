module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianScheme
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_abelianScheme : GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.poincareDeRhamDuality | exact GlobalTheory.poincareDeRhamDuality | (intros; apply GlobalTheory.poincareDeRhamDuality <;> assumption)
