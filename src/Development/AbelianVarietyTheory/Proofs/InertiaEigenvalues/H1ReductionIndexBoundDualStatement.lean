module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDual
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_reduction_index_bound_of_tateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  first | exact @GlobalTheory.BoundedIndex.h1_reduction_index_bounded | exact GlobalTheory.BoundedIndex.h1_reduction_index_bounded | (intros; apply GlobalTheory.BoundedIndex.h1_reduction_index_bounded <;> assumption)
