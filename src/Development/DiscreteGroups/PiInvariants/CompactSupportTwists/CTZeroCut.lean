module

public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.NoPiHk

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS
open GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def GSat (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (φ : Sm E n) : Prop :=
  ∀ w, w ∉ S → FixAt w φ ∧ (B w).card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, ∀ g : GL (Fin n) (w.adicCompletion E),
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then ϖ else 1) →
    ∀ R, IsHk w g R → ∃ m : ℕ, ((hk w R - satEig (qV E w) n (B w) j • (1 : Module.End ℂ (Sm E n))) ^ m) φ = 0

end Defs

def Supp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (φ : Sm E n), IsAutForm φ →
  φ ≠ 0 → ∀ S B, GSat S B φ →
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (σ : ∀ i, CuspSub E (m i)), Nonempty ι ∧ (∀ i, 1 ≤ m i) ∧
    ∀ᶠ w in Filter.cofinite, ∃ Bi : ι → Multiset ℂˣ, (∀ i, (CG.mk (σ i)).HasSat w (Bi i)) ∧ ∑ i, Bi i = B w

end DiscreteGroups.T1.G

end
