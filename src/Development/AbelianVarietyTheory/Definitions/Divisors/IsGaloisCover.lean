module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

def IsTan {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
    y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
    ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
      (∀ l, φ (D ℂ (Sec s' V) (Sec.res s' hV1 (appSec s s' c1 U (t l)))) = Pi.single l 1) ∧
      (∀ j, φ (D ℂ (Sec s' V) (Sec.res s' hV2 (appSec s s' c2 U (t j)))) = fun l => A j l) ∧
      ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

def IsGal {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} (π : W ⟶ Z) (hπ : π ≫ s = sW) (G : Type) [Group G]
    (act : G → (W ⟶ W)) : Prop :=
  GlobalTheory.ZM.IsGaloisCover G (fun g => act g⁻¹) π

namespace IsGal

variable {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} {π : W ⟶ Z} {hπ : π ≫ s = sW} {G : Type} [Group G]
  {act : G → (W ⟶ W)}

theorem mk' (hG : Finite G) (hfin : IsFinite π) (het : Etale π) (hon : Surjective π) (hinv : ∀ g, act g ≫ π = π)
    (hmul : ∀ g h, act (g * h) = act h ≫ act g) (hone : act 1 = 𝟙 W)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W), a ≫ π = b ≫ π → ∃! g : G, b = a ≫ act g) :
    IsGal π hπ G act := by
  refine GlobalTheory.ZM.IsGaloisCover.mk hG ?_ ?_ (fun a => hinv a⁻¹) hfin het hon ?_
  · simpa only [inv_one] using hone
  · intro a c
    simpa only [mul_inv_rev] using hmul c⁻¹ a⁻¹
  · intro K _ _ y y' e
    obtain ⟨g, hg, hu⟩ := hfib K y y' e
    refine ⟨g⁻¹, by simpa only [inv_inv] using hg.symm, fun a ha => ?_⟩
    simpa only [inv_inv] using congrArg Inv.inv (hu a⁻¹ ha.symm)

theorem finite (h : IsGal π hπ G act) : Finite G := GlobalTheory.ZM.IsGaloisCover.finite h
theorem etale (h : IsGal π hπ G act) : Etale π := GlobalTheory.ZM.IsGaloisCover.etale h
theorem surjective (h : IsGal π hπ G act) : Surjective π := GlobalTheory.ZM.IsGaloisCover.onto h

theorem act_comp (h : IsGal π hπ G act) (g : G) : act g ≫ π = π := by
  simpa using GlobalTheory.ZM.IsGaloisCover.inv h g⁻¹

theorem fibre (h : IsGal π hπ G act) (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W) :
    a ≫ π = b ≫ π ↔ ∃! g : G, b = a ≫ act g := by
  constructor
  · intro e
    obtain ⟨g, hg, hu⟩ := GlobalTheory.ZM.IsGaloisCover.fibre h K a b e
    refine ⟨g⁻¹, hg.symm, fun g' hg' => ?_⟩
    have := hu g'⁻¹ (by simpa using hg'.symm)
    simp [← this]
  · rintro ⟨g, hg, -⟩
    rw [hg, Category.assoc, h.act_comp]

end IsGal

end GlobalTheory.W1
