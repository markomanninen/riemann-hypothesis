module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckePointsOfPartsComm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairings
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem heckePoints_of_laws :
    Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        1 ≤ D.p + D.q → ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun hL _ => heckePoints_of_parts_comm hL LiePull.lieMult_pull obj_pull ObjMaps.id_comp_cancel
    obj_isAbelianScheme_dim_rigidified_sym (moduli_rep_of_base ObjMaps.id_comp_cancel)
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale (lam_iso_of_weil_pairings hL)
    (exists_quotient_by_finite_group_of_points hL)

end GlobalTheory
