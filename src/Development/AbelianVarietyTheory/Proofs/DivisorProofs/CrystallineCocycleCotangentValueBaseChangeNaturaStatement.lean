module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueBaseChangeNatura
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.crystallineCocycleCotangentValue_baseChange_natural
    (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R')
    (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ)
    (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D']
    (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D')
    (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (ha : ∀ r : D, (a.φ r : D') = s r) :
    cotVal (m.coef.pullbackOneCocycle f) y' =
      (SemiBialgHom.cot s) (cotVal f y) + dUnit (R := R') (A := D') (ev f a) :=
  cotVal_pull R R' σ X X' φ m D D' s y y' a f ha
