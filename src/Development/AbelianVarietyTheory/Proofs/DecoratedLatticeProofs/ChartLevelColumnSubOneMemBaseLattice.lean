module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.AdForm.level_col_sub_one_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  set_option maxHeartbeats 10000000 in
    next =>
      intro B X I hI hP l Z u a Ch A hA j hj b κ hκ v hv s
      obtain ⟨-, κ', hκ'⟩ := (hA.U j hj b κ).1 hκ
      have hgram : gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
      haveI : NeZero ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) := ⟨by
        have := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_add_three_le_k
        simp only [Ranks.N]; omega⟩
      obtain ⟨At, -, hpi, -⟩ := GlobalTheory.Mem.AtLevel.exists_atTTied I hI hP l Z u
      let sg : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E := RingOfIntegers.mapRingHom (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)
      have hsc : ∀ x, (sg x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.conj (x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
      have hpq : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) * (sg At.piU : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hsc]; exact At.piU_norm
      have hTp := ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T_prime
      have hp0 : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
      have hL : (A.K j hj b).lev.Lb = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) (((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)⁻¹) := by
        refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ At.piU hp0 _ ?_
        rw [hpi]; exact (hA.reads j hj).lb b
      have hx := (((A.K j hj b).lev.U_eq κ'.1).1 κ'.2).2 v
      have hT := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.fixed x).1 hx)
          (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.cmUnram.2.2 hgram (A.K j hj b).lev At.piU (sg At.piU) rfl hpq hTp hL v hv (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u At v hv) _).1 hx
      have hsp : Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb) = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) ((sg At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hL, hgram]; exact GlobalTheory.uLocDual_eq (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (fun x => star_star x) _ At.piU (sg At.piU) hp0 rfl
      have hy : (fun r => Formalism.UG.inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((Pi.single s 1 : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) r)) ∈ Formalism.UG.latS (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (intV (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E v) (Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb)) := by
        simp only [hsp]
        refine Submodule.subset_span ⟨Pi.single s 1, ?_, rfl⟩
        rw [SetLike.mem_coe, Formalism.L2.Col.rll_mem_dLat]
        refine ⟨fun i _ => ?_, ?_⟩
        · by_cases h : i = s
          · subst h; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _
        · by_cases h : Formalism.L2.Col.lastIdx ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) = s
          · rw [h, Pi.single_eq_same, mul_one]; exact ⟨sg At.piU, rfl⟩
          · rw [Pi.single_eq_of_ne h, mul_zero]; exact zero_mem _
      have key := hT.2 _ hy
      convert key using 1
      funext r
      have hm : ((Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) κ'.1 : GL _ _) : Matrix _ _ _) = (κ'.1.1).map (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) := rfl
      rw [Pi.sub_apply, hm, hκ']
      congr 1
      · simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply]
      · simp [Pi.single_apply, Matrix.one_apply]

end
