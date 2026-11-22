module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

theorem push_constMor_pull {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀)
    [IsMonHom g] (c : primDR A₀) :
    primPull (epsDP k) (GlobalTheory.DeRham.epsRed k) g ((constMor A₀).pull c) =
      (constMor A₀).pull (primPull (dp0 k) (𝟙 _) g c) := by
  have K := (constMor A₀).isMor.comp (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor
  apply Subtype.ext
  exact (IsMor.pullback1_comp (constMor A₀).isMor
    (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor K (fun _ ↦ rfl) rfl c.1).trans
    (IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (constMor A₀).isMor K
      (fun _ ↦ rfl) (by simp) c.1).symm

theorem push_mem_graphFil : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (f : HdR A₀ →ₗ[k] HdR A₀), (∀ x ∈ Fil A₀, f (push (dp0 k) (𝟙 _) g x) - push (dp0 k) (𝟙 _) g (f x) ∈ Fil A₀) → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ∈ GlobalTheory.HTRealise.graphFil A₀ f := by
  intro k _ A₀ _ g _ f hf d hd
  obtain ⟨x, hx, y, hy, e⟩ := hd
  refine ⟨push (dp0 k) (𝟙 _) g x, push_mem_Fil g hx,
    push (dp0 k) (𝟙 _) g (f x) - f (push (dp0 k) (𝟙 _) g x) + push (dp0 k) (𝟙 _) g y,
    add_mem (by rw [← neg_sub]; exact neg_mem (hf x hx)) (push_mem_Fil g hy), fun c ↦ ?_⟩
  rw [push_apply, push_constMor_pull, e]
  simp only [push_apply, LinearMap.add_apply, LinearMap.sub_apply]
  congr 2
  ring

end GlobalTheory.HTRealise
