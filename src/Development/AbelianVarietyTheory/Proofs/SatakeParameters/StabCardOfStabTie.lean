module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AmbientLatticeAvoidance
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

noncomputable section

namespace GlobalTheory.KFormsCmp

section Cong

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

end Cong

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}






end Red

section Primes

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_of_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

theorem g_mem_of_vGs (hP : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ∃ k, (Pr.g k : 𝓞 X.E) ∈ w.asIdeal := by
  classical
  rcases Finset.mem_union.1 hw with h | h
  · exact ⟨0, hP.g_mem h⟩
  · exact ⟨1, hP.g_mem h⟩

theorem disj (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (hg : ∀ k, Pr.g k ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hQ : P ∈ QE sel (mu : Chr X.F X.E X.K)) : P ∉ Pr.vGs := fun hw => by
  obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
  exact notMem_of_QE hs mu hQ (hP.g_prime k) (hg k) hk

end Primes

section Top

variable {E : Type} [Field E] {a n : ℕ}

end Top

section Levels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)



variable {T}

end Levels

section Points

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev APt (i : ℕ) : Type := AmbientLatticeAvoidance.Pt (R := D.R) T.sel T.xi T.L T.w i


variable {T}

end Points

section Moves

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)
  (abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R)))
  (dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ)

variable {T abelian₂ dep}

end Moves

section Classes

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}


variable {rep : ∀ i, (D.chTw u μ).cls i → APt T i}


end Classes

section Kernels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {rep : ∀ i, (D.chTw u μ).cls i → APt T i}




variable {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}

end Kernels

end GlobalTheory.KFormsCmp
