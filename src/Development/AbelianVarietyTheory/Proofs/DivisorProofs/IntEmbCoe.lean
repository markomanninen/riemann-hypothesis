module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def IsRosati (c : O →+* O) {S : Scheme.{0}} (P : Out.PolAV S) (j : OAct O P.A) : Prop :=
  ∀ a, Out.RosatiAdj P.A P.L (j.act a) (j.act (c a))

def PolPart (c : O →+* O) {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (T : TorusExtension G) (P : Out.PolAV (Sp K)) (e : T.B ≅ P.A) (j : OAct O P.A),
    IsMonHom (T.q ≫ e.hom) ∧ (∀ a, i.act a ≫ T.q ≫ e.hom = (T.q ≫ e.hom) ≫ j.act a) ∧ IsRosati c P j

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

def geomGenPt (C : Scheme.{0}) [IsIntegral C] : Sp (AlgebraicClosure C.functionField) ⟶ C :=
  spMap (algebraMap C.functionField (AlgebraicClosure C.functionField)) ≫ genPt C

def PolGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (G' : Over (Sp (AlgebraicClosure C.functionField))) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left),
    IsActPull i' i (geomGenPt C) φ ∧ PolPart c i'

def AbGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (P : Out.PolAV (Sp C.functionField)) (j : OAct O P.A) (φ : P.A.left ⟶ G.left),
    IsActPull j i (genPt C) φ ∧ IsRosati c P j

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
