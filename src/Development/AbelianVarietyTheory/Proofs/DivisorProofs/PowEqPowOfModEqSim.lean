module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime]

structure SimSys (D : Datum p) (N K : ℕ) where
  g : ℕ → D.La →+ D.La
  u : ℕ → ℕ
  lin : ∀ n, 0 < n → n.Coprime p → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  u_cop : ∀ n, 0 < n → n.Coprime p → (u n).Coprime n
  u_tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n]
  surj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w
  sim : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - u n * D.EF x y
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z
  one : ∀ x, ∃ z, g K x = x + N • z

variable {D : Datum p} {N K : ℕ}

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem TateIsoO.ev_nsmul_self (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (z : D.La) :
    I.ev n (n • z) = 1 :=
  (I.ker n hn hc _).2 ⟨z, rfl⟩

theorem TateIsoO.ev_add_nsmul (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (x z : D.La) :
    I.ev n (x + n • z) = I.ev n x := by
  rw [I.add, I.ev_nsmul_self hn hc, _root_.mul_one]

end Tate

variable {R : Type} [CommRing R]


variable (D K) in
def multSub : AddSubgroup D.La where
  carrier := {x | ∃ z, x = K • z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨c, rfl⟩
    exact ⟨a + c, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (smul_neg _ _).symm⟩


variable (D K) in
abbrev LQ := D.La ⧸ multSub D K


end GlobalTheory.UPel.HT
