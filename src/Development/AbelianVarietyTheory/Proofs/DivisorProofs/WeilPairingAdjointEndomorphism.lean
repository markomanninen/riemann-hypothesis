module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilAdjoint

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem weilIs_algHom {K : Type} [CommRing K] {B : Over (Sp K)} [GrpObj B] (hB : IsAbelianScheme B) {P : LB B.left}
    (hP : P.IsLB) {k : ℤ} {D E : Type} [CommRing D] [Algebra K D] [CommRing E] [Algebra K E] (α : D →ₐ[K] E)
    {x y : SpAlg K D ⟶ B} {x' y' : SpAlg K E ⟶ B} (hx : spOver α ≫ x = x') (hy : spOver α ≫ y = y') {U : Dˣ}
    (hU : Out.WeilIs B P k (T := SpAlg K D) x y (unitOn U)) :
    Out.WeilIs B P k (T := SpAlg K E) x' y' (unitOn (Units.map (α : D →+* E).toMonoidHom U)) := by
  rw [← map_unitOn, ← hx, ← hy]
  exact CommPairing.weilIs_pull GlobalTheory.globalFns_holds hB hP (T := SpAlg K D) (T' := SpAlg K E) (spOver α) hU

end GlobalTheory.WeilAdjoint
