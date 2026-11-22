module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjective
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V], Function.Surjective (monV P ℚ_[l] V) := by
  first | exact @GlobalTheory.PMon.monV_surjective_onto | exact GlobalTheory.PMon.monV_surjective_onto | (intros; apply GlobalTheory.PMon.monV_surjective_onto <;> assumption)
