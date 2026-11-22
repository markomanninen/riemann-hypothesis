module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_linear_generated_by_transvections : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) → ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R), u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  first | exact @GlobalTheory.GLGen.mem_of_det_eq_one | exact GlobalTheory.GLGen.mem_of_det_eq_one | (intros; apply GlobalTheory.GLGen.mem_of_det_eq_one <;> assumption)
