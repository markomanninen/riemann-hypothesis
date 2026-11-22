module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemMaximalIdealBall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

def RootsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso Dw k Q act e)
    (z : ℕ → kˣ), 1 ≤ Dw.p + Dw.q → (∀ n, 0 < n → IsPrimitiveRoot (z n) n) →
    (∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n) → z l.A = I.ζ l.A →
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} {ct : At S κ p}

variable {Z : ct.Mdl} {y : DVP ct} {e : Ext y}

end GlobalTheory.LocM.Cht
