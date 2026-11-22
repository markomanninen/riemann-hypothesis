module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AinfValueOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal

theorem ginfTest_holds : GinfTest := by
  intro D X hb FdN FdN' u u' hX
  obtain ⟨K, hK, h0, -⟩ := muInf_compact_pos X
  have hc : Continuous (X.toInf hb) := by
    unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
    exact continuous_fst.comp ((MassDataMassesW.continuous_splitA _ _).comp
      ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))
  have hm : Measurable (X.toInf hb) := by
    haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
    exact hc.measurable
  have hG : X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb) := hX.1.2.1
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  refine ⟨toMeasurable X.measG.μGinf (X.toInf hb '' K), measurableSet_toMeasurable _ _, ?_, ?_⟩ <;>
    rw [measure_toMeasurable]
  · calc (0 : ENNReal) < Formalism.L2.SG.ProjRows.muInf X.B.I K := h0
      _ ≤ Formalism.L2.SG.ProjRows.muInf X.B.I (X.toInf hb ⁻¹' (X.toInf hb '' K)) :=
          measure_mono (Set.subset_preimage_image _ _)
      _ ≤ ((Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb)) (X.toInf hb '' K) :=
          Measure.le_map_apply hm.aemeasurable _
      _ = X.measG.μGinf (X.toInf hb '' K) := by rw [hG]
  · exact (hK.image hc).measure_lt_top

def HinfFin : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → (X.measW u').μHinf Set.univ < ⊤

theorem htotInf_of (hF : HinfFin) : HtotInf := by
  intro D X hb FdN FdN' u u' hX
  have e1 : (X.measW u').μHinf Set.univ = X.muH u' Set.univ := by
    have hc : Continuous (X.toInf hb) := by
      unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
      exact continuous_fst.comp ((MassDataMassesW.continuous_splitA _ _).comp
        ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))
    have hm : Measurable (X.toInf hb) := by
      haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
      exact hc.measurable
    have h := (hX.1.2.2.2 u').2
    have h1 := congrArg (fun m => m Set.univ) h
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at h1
    rw [← h1]
    unfold Formalism.L2.SG.Measures.amb
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  refine ⟨e1, Measure.measure_univ_pos.2 (X.muH_haar u').2.1, e1 ▸ hF X hb FdN FdN' u u' hX⟩

theorem hinfFin_of (hC : MassDataMassesW.HinfCompact) : HinfFin := by
  intro D X hb FdN FdN' u u' hX
  have hH : (X.measW u').μHinf.IsHaarMeasure := (X.measW_norm u').2.1
  have hc : CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := hC X u'
  exact @IsCompact.measure_lt_top _ _ _ _ hH.toIsFiniteMeasureOnCompacts _ (@isCompact_univ _ _ hc)

end PI.AprimeInfW
