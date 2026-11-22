module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AtTLemmas

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem SameAt.symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

theorem SameAt.trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', k1, k2⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]
    exact h1 _ (k1 _ hx)
  · rw [mul_smul]
    exact k2 _ (h2 _ hx)

theorem SameAt.sup {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (S : Submodule (𝓞 E) (Sp E n)) : SameAt Q (N ⊔ S) (N' ⊔ S) := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)

end Loc

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
