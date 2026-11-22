module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibre
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_h1_nakayama_closed_fibre : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  first | exact @GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero | exact GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero | (intros; apply GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero <;> assumption)
