module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
