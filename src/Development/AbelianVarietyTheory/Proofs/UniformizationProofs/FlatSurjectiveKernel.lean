module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

namespace GlobalTheory.GtCoordCompare

section Calc

variable {Y W W' Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {ψ : K → (W ⟶ Y)} {ψ' : K → (W' ⟶ Y)}
  {ε ε' : K → ℤ} {r : Z ⟶ W} {r' : Z ⟶ W'}

end Calc

section Image

variable {Y G B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] (q : G ⟶ B) {φ : K → (B ⟶ Y)} {φ' : K → (G ⟶ Y)}
  {ε ε' : K → ℤ}

variable {q} {x : LB.Gen (LB.LinComb L φ' ε')} {V : B.Opens}


end Image

section Group

variable {S Y : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B] {q : G ⟶ B}
  {i : splitTorus S X ⟶ G} {L : LB Y} {K : Type} [Fintype K] {ε ε' : K → ℤ}

def WtGen (i : splitTorus S X ⟶ G) {φ' : K → (G.left ⟶ Y)} (x : LB.Gen (LB.LinComb L φ' ε')) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
    val x ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val x g.left z J

theorem act_comp [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hi, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  exact congrArg (fun f => f.left) e

theorem isWt_of_gs {V : G.left.Opens} {a : Γ(G.left, V)} {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ∀ z : Z.left,
      gs ((t ≫ i) * g).left z V a = (gm t.left z ⊤ (charUnit S X χ)).val * gs g.left z V a) : IsWt i V a χ :=
  fun Z t g h₁ h₂ => fn_ext fun z hz => by
    rw [gs_mul _ z _ hz, gs_appLE _ _ _ _ _ z hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp, Category.id_comp,
      h Z t g h₂ z]
    congr 1
    refine ((gs_pull (𝟙 _) t.left z ⊤ trivial _).trans ?_).symm
    rw [Category.id_comp, gs_unit _ z ⊤ trivial]

section One

variable [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) (hL : L.IsLB) {φ : K → (B.left ⟶ Y)} {φ' : K → (G.left ⟶ Y)}
  (hφ : ∀ k, φ' k = q.left ≫ φ k) {x : LB.Gen (LB.LinComb L φ' ε')} (hx : x.IsGen) {χ : X} (hw : WtGen i x χ)
include hi hL hφ hx hw


end One

section All

variable [IsMonHom q] [IsMonHom i] [IsAffineHom q.left] (hL : L.IsLB) (hε : ∀ k, ε' k = -ε k)
  {φ : X → K → (B.left ⟶ Y)} {φ' : X → K → (G.left ⟶ Y)} (hφ : ∀ χ k, φ' χ k = q.left ≫ φ χ k)
  {x : ∀ χ, LB.Gen (LB.LinComb L (φ' χ) ε')} (hx : ∀ χ, (x χ).IsGen) (hw : ∀ χ, WtGen i (x χ) χ)
include hL hε hφ hx hw


end All

end Group

end GlobalTheory.GtCoordCompare
