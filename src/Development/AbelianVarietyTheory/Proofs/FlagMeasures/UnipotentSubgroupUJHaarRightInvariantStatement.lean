module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_subgroup_UJ_haar_right_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  first | exact @GlobalTheory.UJUnimod.unimodular_of_unipotent | exact GlobalTheory.UJUnimod.unimodular_of_unipotent | (intros; apply GlobalTheory.UJUnimod.unimodular_of_unipotent <;> assumption)
