module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AtTLemmas

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


theorem Deco.L_dia (d : Deco E n ST SG) (c : DiaG (E := E) (ST := ST)) : (d.dia c).L = d.L := by
  unfold Deco.L
  congr 1
  ext x
  show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)
  simp only [Units.mul_right_eq_zero]

theorem Deco.Lsh_dia (d : Deco E n ST SG) (c : DiaG (E := E) (ST := ST)) : (d.dia c).Lsh = d.Lsh := by
  unfold Deco.Lsh
  rw [Deco.L_dia]

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

section Adj

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Adj

section AtW

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtW

end Formalism.L2.Col
