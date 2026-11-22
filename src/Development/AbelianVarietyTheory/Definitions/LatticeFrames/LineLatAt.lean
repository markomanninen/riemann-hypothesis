module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

def idV (𝔞 : FI D) (v : Pl D) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ w, w ≠ v → evalV D.host.F w α = 0) ∧ ∃ a ∈ 𝔞,
    y = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a}

def dI (D : D7) : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar

def cI (D : D7) (j : ℕ) : FI D :=
  FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (j / 2)) * (D.host.AA * D.host.AAbar⁻¹) ^ ((D.R.m - j) / 2)

def bI (D : D7) (j ρ i : ℕ) : FI D := dI D ^ (ρ - i) * cI D j

def MonoId {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) : Prop :=
  MonoAt d L L₀ v ∧ ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a ∈ idV (𝔟 i) v

def LineId {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a ∈ idV 𝔠 v

def LineLatAt (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (LL : Lat L) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV ζ ∈ latV L LL (· = v) ↔ a ∈ idV 𝔠 v

variable {a : XPart D u}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {o : OffX a k ι} {b : YPart a}



theorem idV_mono {𝔞 𝔟 : FI D} (h : 𝔞 ≤ 𝔟) (v : Pl D) : idV 𝔞 v ≤ idV 𝔟 v := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, hv, x, hx, rfl⟩
  exact ⟨α, hα, hv, x, h hx, rfl⟩

theorem idV_zero (v : Pl D) : idV (0 : FI D) v = ⊥ := by

  rw [idV, AddSubgroup.closure_eq_bot_iff]
  rintro y ⟨α, -, -, x, hx, rfl⟩
  obtain rfl : x = 0 := by simpa using hx
  simp

end GlobalTheory.SeeSaw

end
