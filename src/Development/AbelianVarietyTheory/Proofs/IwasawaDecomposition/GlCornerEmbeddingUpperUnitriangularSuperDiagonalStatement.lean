module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  first | exact @GlobalTheory.CornerUnip.corner_unipB_superDiag | exact GlobalTheory.CornerUnip.corner_unipB_superDiag | (intros; apply GlobalTheory.CornerUnip.corner_unipB_superDiag <;> assumption)
