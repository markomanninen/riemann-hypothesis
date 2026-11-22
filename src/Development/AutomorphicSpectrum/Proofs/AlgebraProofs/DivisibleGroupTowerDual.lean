module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsBialgHom

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

open Coalgebra WithConv

theorem exists_hom_dual_of_pairingExtends : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := PositivityTheory.HtPt.Twpol.exists_linear
      (X.A n) (e n) (lev p n) (fun a => (τ a).pt n) (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := PositivityTheory.HtPt.Twpol.exists_bialgHom (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add]) (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ

end GlobalTheory.CompanionTheory.Ar.HT
