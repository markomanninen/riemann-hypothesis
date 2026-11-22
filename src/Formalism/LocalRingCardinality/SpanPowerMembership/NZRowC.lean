module

public import Formalism.LocalRingCardinality.DataBu
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataForms

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

section Rows

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
  (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
  (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
  (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
  (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w)

end Rows

section RowsLemmas

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] {embLL : LL →+* ℂ} {P : Rows.Places LL}
  {Tau : Type} [Fintype Tau] {hTau : Fintype.card Tau = R.f} {Dst : ℝ}
  {sha : ℕ → ℕ → ℚ} {hsha : ∀ l e, 0 ≤ sha l e} {cg : ℕ} {hcg : 0 < cg}
  {kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ} {ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ}
  {tw : P.Pl → Bool} {htw : ∀ w, tw (P.conj w) = tw w}
  {Word : Type} {cI : Word → Type} [∀ u, Fintype (cI u)] {d Dall d0 : ℕ} {hd : d ≤ Dall}
  {FT : Type} [Fintype FT] [DecidableEq FT] {ft : Fin d → FT} {ft0 : Fin d0 → FT}
  {per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ}
  {eta : ℕ → P.Pl → ℚ} {heta : ∀ j w, 0 ≤ eta j w}

end RowsLemmas

section Gen

variable {R : Ranks} (D : Rows.Data R)

end Gen

end Formalism.BasicNotions.Examples₂.NZ
