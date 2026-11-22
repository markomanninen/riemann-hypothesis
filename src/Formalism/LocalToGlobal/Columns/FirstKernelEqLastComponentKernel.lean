module

public import Formalism.LocalToGlobal.Columns.GFamEv
public import Formalism.LocalToGlobal.Columns.StabMapRLInjective
public import Formalism.LocalToGlobal.Columns.RecChainCUnfPol
public import Formalism.LocalToGlobal.Columns.RefXi1Above
public import Formalism.LocalToGlobal.Columns.RecChainYUnfPol
public import Mathlib

@[expose] public section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)


include hQ in
theorem rcol_rowSG_eq : Pr.vGs = rowSG Pr sel mu := by
  classical
  unfold rowSG uSG
  rw [hQ, Finset.union_empty]

end Defs

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}
  (hX : X.Ok) {Gc : ChGlob X R.m} (hL : L.Ok Ch sel mu cst Gc m2) (h0 : Λ 0 = colLev Ch 0)
  (hΛ : ∀ j, j ≤ m2 + 1 → ∀ b : L.β j, L.levG j b = Λ j) (h1 : ∀ j, j ≤ m2 + 1 → ∀ b b' : L.β j, b = b')
  (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
  {b₁ : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b₁} {P : LevFam X.E X.K R.r Pr.vGs}
  (hK : KerEquivC W Ch sel mu cst L Am u m2 b₁ hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (φ : MfV W Ch u)

end Main

end Formalism.L2.Col
