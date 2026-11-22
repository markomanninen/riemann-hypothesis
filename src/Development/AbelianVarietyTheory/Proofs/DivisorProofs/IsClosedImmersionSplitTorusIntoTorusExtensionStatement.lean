module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension : ∀ (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω))) [GrpObj H], TorusExtension H → ∀ (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H), IsMonHom v → (∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 → GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) → IsClosedImmersion v.left := by
  first | exact @GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | exact GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | (intros; apply GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension <;> assumption)
