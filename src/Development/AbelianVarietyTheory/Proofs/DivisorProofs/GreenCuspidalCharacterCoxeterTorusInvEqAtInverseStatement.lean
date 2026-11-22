module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenCuspidalCharacterCoxeterTorus_inv_eq_at_inverse : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)), h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  first | exact @GlobalTheory.CuspInv.cuspChar_inv | exact GlobalTheory.CuspInv.cuspChar_inv | (intros; apply GlobalTheory.CuspInv.cuspChar_inv <;> assumption)
