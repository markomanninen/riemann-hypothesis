module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory


open TorusNil TorusLocal in
theorem splitTorus_hom_ext_of_forall_pow (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R)))
    (hB : IsSeparated B.hom) (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B)
    (hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) : f = g := by
  set t := torusPt R A (AddMonoidAlgebra.of R A) with ht
  have h1 : t ≫ f = t ≫ g := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap R (AddMonoidAlgebra R A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map
          (algebraMap R (AddMonoidAlgebra R A)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of R A
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
