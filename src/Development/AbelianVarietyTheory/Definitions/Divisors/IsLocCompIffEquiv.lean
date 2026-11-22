module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
