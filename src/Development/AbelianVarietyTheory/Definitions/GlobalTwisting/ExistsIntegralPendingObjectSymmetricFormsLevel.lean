module

public import Mathlib
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.PendExample

open Formalism.BasicNotions Classical NumberField GlobalTheory.MemberTorsor
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

section Span
variable (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

variable {D lam}


variable {g : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ}

end Span

section Lat
variable (K : Type) [Field K] [NumberField K] [StarRing K] (κ : Type) [Fintype κ] [DecidableEq κ]

variable {K κ}

end Lat

section Chain
variable (D : D7) (u : D.what₂.Word) (T : ℕ) [Fact T.Prime]

end Chain

theorem nfAll_pos {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ≠ 0) : 0 < (nfAll l p p).re := by
  unfold nfAll
  simp only [fockF_self_eq (extremal ℂ n _)]
  rw [← Complex.ofReal_prod, Complex.div_ofReal_re]
  refine div_pos (fockF_self_pos hp) (Finset.prod_pos fun τ _ => ?_)
  have := fockF_self_pos (f := extremal ℂ n (l τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (l τ).natW)
  rwa [fockF_self_eq, Complex.ofReal_re] at this

end GlobalTheory.LvT.PendExample
