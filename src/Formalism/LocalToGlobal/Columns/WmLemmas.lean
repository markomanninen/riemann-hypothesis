module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
public import Formalism.LocalToGlobal.Columns.HeckeSpCount
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Columns.GSetLemmas

@[expose] public section

open NumberField IsDedekindDomain Module Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nb

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (V : Type) [AddCommGroup V] [Module X.K V]

theorem trF_nbFun (a : GLG (E := X.E) (n := n) (SG := SG)) (P : Ideal (𝓞 X.E)) (i : ℕ) (ψ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → V) :
    trF X n ST SG V a (nbFun X.K V P i ψ) = nbFun X.K V P i (trF X n ST SG V a ψ) := by
  funext d
  rw [trF_apply]
  show ∑ d₁ ∈ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d).heckeNb P i, ψ d₁ =
    ∑ d₁ ∈ d.heckeNb P i, ψ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d₁)
  set g : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) := ((1 : UF X.E n), a⁻¹)
  refine Finset.sum_nbij' (fun e => g⁻¹ • e) (fun e => g • e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have : g • (g⁻¹ • e) ∈ (g • d).heckeNb P i := by rwa [smul_inv_smul]
    exact (DecoSet.smul_mem_heckeNb_iff g).1 this
  · intro e he
    exact (DecoSet.smul_mem_heckeNb_iff g).2 he
  · intro e _
    exact smul_inv_smul g e
  · intro e _
    exact inv_smul_smul g e
  · intro e _
    rw [smul_inv_smul]

end Nb

section Poly

variable {L : Type} [Field L]

end Poly

section HV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end HV

section FromRel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end FromRel

section Inh

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Inh

section Fub

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Fub

section Rev

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


end Rev

section PhiLem

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {K : Type} [Field K] {a b : ℕ}


end PhiLem

section Gauss

variable {L : Type} [Field L]

end Gauss

section Count

variable (E : Type) [Field E] [NumberField E] [StarRing E]


end Count

section ClassRel

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ClassRel

section RelOf

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end RelOf

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Main

end Formalism.L2.Col
