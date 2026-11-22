module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.PullPull

section Sections

variable {X Y Z : Scheme.{0}}

theorem pullbackComp_hom_app (b : Z ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : Z.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h s]
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a).hom.app E = 𝟙 _ := by simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

end Sections

section Met

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E E' : X.Modules} {r : ℕ}

end Met

end GlobalTheory.PullPull

namespace GlobalTheory.VMetric

end GlobalTheory.VMetric
