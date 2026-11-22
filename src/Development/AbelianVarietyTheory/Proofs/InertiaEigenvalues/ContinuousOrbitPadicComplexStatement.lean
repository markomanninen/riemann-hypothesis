module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_orbit_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ y : PadicComplex l, Continuous (fun g => act g y) := by
  first | exact @GlobalTheory.Cyc.IsActC.continuous_orbit | exact GlobalTheory.Cyc.IsActC.continuous_orbit | (intros; apply GlobalTheory.Cyc.IsActC.continuous_orbit <;> assumption)
