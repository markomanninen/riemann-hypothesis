module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Branches

variable {X X' : Scheme.{0}}

def pre (π : X' ⟶ X) (Z : Closeds X) : Closeds X' := Z.preimage π.continuous

abbrev van (Z : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x

def tr {x y : X} (h : x = y) : X.presheaf.stalk x →+* X.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom

def IsRsp {A : Type} [CommRing A] [IsLocalRing A] {ι : Type} [Fintype ι] (f : ι → A) : Prop :=
  IsRegularLocalRing A ∧ Ideal.span (Set.range f) = maximalIdeal A ∧ (Fintype.card ι : WithBot ℕ∞) = ringKrullDim A

def BrAt (B : Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x) : Prop :=
  IsRsp f ∧ van B x = Ideal.span {∏ j, f (Sum.inl j)}

def ColAt (B : Closeds X) {ι : Type} (E : ι → Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x)
    (c : Fin m → ι) : Prop :=
  BrAt B x f ∧ ∀ i, van (E i) x = Ideal.span {∏ j ∈ Finset.univ.filter (fun j => c j = i), f (Sum.inl j)}

def IsStrict (B : Closeds X) {ι : Type} (E : ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → ι), ColAt B E x f c ∧ Function.Injective c

end Branches

section Pairs

variable {K F : Type} [Field K] [Field F] {XK X X'K X' : Scheme.{0}}

end Pairs

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsCN (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ CharZero R

abbrev toBase {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp R)) :=
  Over.homMk (spMap φ) (Category.comp_id _)

end Sections

section Steps

def HomExtNormalSt : Prop :=
  ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
    ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f

def PullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsCN R' → Function.Injective φ → IsLocalHom φ → P.TorsionIso →
    ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (P' : PELUnif (maximalIdeal R') t')
      (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X), P'.TorsionIso ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)

end Steps

end GlobalTheory.TorRef
