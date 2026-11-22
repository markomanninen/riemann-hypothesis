module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmExistsOnOfPointCarriesObject

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem exists_cmObj_baseChange : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (K₂ : Type) [Field K₂] [NumberField K₂] (i : K →+* K₂) (σ₂ : K₂ →+* ℂ), σ₂.comp i = σ₁ → ∃ (ρ₂ : 𝓞 K₂) (X₂ : GlobalTheory.CM.CMObj H K₂ ρ₂ σ₂ p q) (_ : SABMap X₂.B.t X.B.t (spMap (RingOfIntegers.mapRingHom i))), (ρ₂ : K₂) = i (ρ : K) ∧ X₂.hh = X.hh := by
  intro _ E _ _ _ H K _ _ ρ σ₁ p q X K₂ _ _ i σ₂ h
  have extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ}
      (X : GlobalTheory.CM.CMObj H K ρ σ p q) (j : K →+* K₂) (σ' : K₂ →+* ℂ)
      (h : σ'.comp j = σ) :
      ∃ (X' : GlobalTheory.CM.CMObj H K₂ (RingOfIntegers.mapRingHom j ρ) σ' p q)
        (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
        (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
        X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := open GlobalTheory.CM GlobalTheory.CMExistsCompare in by
    set f := RingOfIntegers.mapRingHom j with hf
    have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
    choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
    obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
    have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
    choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
    have hpt := spMap_int j h
    refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K₂ j X.split |>.1
              ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
              A := A', B := B'
              typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
              typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
              typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
              hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
    · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
      have e := congrArg Over.Hom.left ((X.lin i).2 c)
      simp only [Over.comp_left] at e
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
        (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
    · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
      choose pA hA using fun b => exists_ptEquiv (a b) hpt
      obtain ⟨x, hx⟩ := X.onto (pB y)
      refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
      rw [hx, map_list_prod, List.map_ofFn]
      congr 2
      funext i
      apply Over.OverMorphism.ext
      simp only [Function.comp_apply]
      rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
      erw [hφ]
      rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
    · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
        (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
        ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
      rw [hpt]
      exact X.weil i
  obtain ⟨X₂, -, mb, hh, -⟩ := extend X i σ₂ h
  exact ⟨_, X₂, mb, rfl, hh⟩

end GlobalTheory.ArcCM
