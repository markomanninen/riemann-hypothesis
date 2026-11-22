module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Imports
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsAlt

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.ChainLattice
