module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt),
      PtExt.IsCan t c x → PtExt.IsCan t c' x' → PtExt.IsCan t (c + c') (x + x')) ∧
    ∀ (r : R) (c : primDR A) (x : G.RigExt), PtExt.IsCan t c x → PtExt.IsCan t (r • c) (r • x) :=
  PtExt.isCan_add_smul R A p G t
