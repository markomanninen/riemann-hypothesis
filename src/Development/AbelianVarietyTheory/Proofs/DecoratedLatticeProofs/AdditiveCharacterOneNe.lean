module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Formalism.LocalToGlobal.Columns.ChainOneOk
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
