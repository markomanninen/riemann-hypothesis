module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToForms
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluationMap_trueChain_forms_to_forms :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I →
      ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (l0 : TC.Law0 I l)
        (u : B.Word) (a : I.ι),
        (∀ φ ∈ ((TC.tw I l l0 Z).fm u a).Fi B.R.m,
          GlobalTheory.PerQ.PtT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u a φ ∈
            ((TC.tw I l l0 Z).fm u a).ptC) ∧
        ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).SgInterlace := by
  intro B X I _ l Z l0 u a
  have hs : ∀ τ, (TC.perIn I u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hW := GlobalTheory.LvT.BuiltChain.weights_ok (TC.perIn I u a) (B.hcW u) B.fields.emb hs
  refine ⟨?_, ?_⟩
  · intro φ hφ
    let M := TC.fm I l u a
    have latticeImage : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x hx
      obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := TC.perIn I u a)
        B.fields.emb B.embLL (B.hcW u) GlobalTheory.LvT.BuiltChain.branching_ok
        (l.ch u a) (l.per u a) (fun τ => (hW τ).1) (fun τ => (hW τ).2)
        ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
      exact ⟨y, hy⟩
    have rationalImage : ∀ x, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x
      have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
        rw [(M.lat_good B.R.m).2.2]
        trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact latticeImage x hx
      | zero => exact ⟨0, by simp⟩
      | add x x' _ _ hx hx' =>
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', by rw [map_add, map_add, map_add, map_add, hy, hy']⟩
      | smul r x _ hx =>
        obtain ⟨y, hy⟩ := hx
        refine ⟨r • y, ?_⟩
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hy, LinearMap.map_smul, LinearMap.map_smul]
    have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    have hφ' : φ ∈ M.Fi B.R.m := hφ
    rw [← (M.emb_basis B.R.m).2] at hφ'
    have hle : Submodule.span ℂ (Set.range fun c => M.emb B.R.m ((M.lat B.R.m).b c)) ≤
        M.ptC.comap ((TC.per I l u a).lowerMap ∘ₗ (TC.per I l u a).evz) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨y, hy⟩ := rationalImage ((M.lat B.R.m).b c)
      show (TC.per I l u a).lowerMap ((TC.per I l u a).evz _) ∈ M.ptC
      rw [← hy]
      exact ptMem y
    exact hle hφ'
  · intro τ i
    obtain ⟨ha, hb⟩ := (hW τ).1 i
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT,
      GlobalTheory.Mem.Col2.shW] at ha hb
    constructor
    · show (B.wts.sgW τ).w i ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩
      change 0 ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ).w i + _) at hb
      linarith
    · show (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ).w i
      change 0 ≤ (B.wts.sgW τ).w i + _ - ((Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
      linarith
