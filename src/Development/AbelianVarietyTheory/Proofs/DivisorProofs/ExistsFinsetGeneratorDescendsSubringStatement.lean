module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetGeneratorDescendsSubring
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_generator_descends_subring : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_finset_gen_descends | exact GlobalTheory.exists_finset_gen_descends | (intros; apply GlobalTheory.exists_finset_gen_descends <;> assumption)
