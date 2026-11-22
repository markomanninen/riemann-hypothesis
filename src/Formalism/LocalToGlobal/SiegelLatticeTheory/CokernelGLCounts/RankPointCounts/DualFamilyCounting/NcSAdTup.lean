module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitSk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousHAIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.AdTupPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.L2.SG.Pf.NcS.SplitSk
open scoped TensorProduct

open scoped Pointwise in
private theorem compact_open_of_haar_pos_finite {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] (hpos : 0 < μ H) (hfin : μ H < ⊤) :
    IsCompact (H : Set G) ∧ IsOpen (H : Set G) := by
  have hopen : IsOpen (H : Set G) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    simpa only [coe_div_coe H] using
      Measure.div_mem_nhds_one_of_haar_pos_ne_top μ (H : Set G) hH.measurableSet hpos hfin.ne
  have hhalf := ENNReal.half_lt_self hpos.ne' hfin.ne
  obtain ⟨K, hKH, hKc, hKm⟩ := hH.measurableSet.exists_lt_isCompact_of_ne_top hfin.ne hhalf
  have hmass : μ H < μ K + μ K := calc
    μ H = μ H / 2 + μ H / 2 := (ENNReal.add_halves _).symm
    _ < μ K + μ K := ENNReal.add_lt_add_of_le_of_lt (hhalf.trans hfin).ne hKm.le hKm
  -- Every translate of K by an element of H meets K, since K has more than half the mass of H.
  have hdiv : Continuous (fun p : G × G => p.1 / p.2) := continuous_fst.div' continuous_snd
  refine ⟨((hKc.prod hKc).image hdiv).of_isClosed_subset hH ?_, hopen⟩
  intro g hg
  have htranslate : g • K ⊆ (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem hg (hKH hx)
  have hmeet : ¬ Disjoint (g • K) K := by
    intro hd
    have hle := measure_mono (μ := μ) (Set.union_subset htranslate hKH)
    rw [measure_union hd hKc.isClosed.measurableSet, measure_smul] at hle
    exact hmass.not_ge hle
  obtain ⟨y, hy, hyK⟩ := Set.not_disjoint_iff.mp hmeet
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
  exact ⟨(g * x, x), ⟨hyK, hx⟩, div_eq_iff_eq_mul.mpr rfl⟩

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
private theorem kf_eq_preimage_stabGLHat (Λ : Set (Fin n → E)) :
    (Kf σ J Λ : Set (HA (Af F) σ J)) = incAf σ J ⁻¹' MassDataMassesW.KCptW.stabGLHat (F := F) Λ :=
  Set.ext fun g => MassDataMassesW.KCptW.kf_iff σ J Λ g

private theorem isClosed_kf [FiniteDimensional F E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    IsClosed (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
  let M := MassDataMassesW.KCptW.latHat (F := F) (L : Set (Fin n → E))
  have hM : IsClosed M := by
    have hEq : M = ⋂ v, MassDataMassesW.KCptW.pv v ⁻¹'
        (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [M, MassDataMassesW.KCptW.latHat]
    rw [hEq]
    refine isClosed_iInter fun v => ?_
    have : T2Space (Fv F v ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Fv F v)
    exact (MassDataLevelSSteps.LatTop.isCompact_latLoc v L hfg).isClosed.preimage
      (MassDataMassesW.KCptW.continuous_pv v)
  have hS := MassDataLevelSSteps.LatTop.isClosed_matStab hM
  rw [kf_eq_preimage_stabGLHat]
  exact ((hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)).preimage
    (continuous_subtype_val : Continuous (incAf σ J))

theorem kf_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    IsCompact (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) ∧
      IsOpen (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hO : MassDataMassesW.KCptW.LatHatOpen :=
    MassDataMassesW.KCptW.latHatOpen_of @MassDataMassesW.KCptW.stdHatOpen_holds
  have hC : MassDataMassesW.KCptW.LatHatCompact :=
    MassDataMassesW.KCptW.latHatCompact_of @MassDataMassesW.KCptW.stdHatCompact_holds
  letI : Submodule.IsFullLattice E L := hL
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ :=
    Submodule.IsFullLattice.span_eq_top
  have hMo := hO (F := F) L hspan hL.fg
  have hMc := hC (F := F) L hspan hL.fg
  have hinc : Continuous (incAf σ J) := continuous_subtype_val
  rw [kf_eq_preimage_stabGLHat]
  refine ⟨?_, (MassDataMassesW.KCptW.isOpen_stabGLHat L hMc hMo).preimage hinc⟩
  exact (PI.AdicCompletionValuation.isClosed_HR (Af F) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (MassDataMassesW.KCptW.isCompact_stabGLHat L hspan hMc)

theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [FiniteDimensional F E] {a : ℕ} (X : Fin a → Fin n → E) :
    IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have : T2Space (R ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product R
  have hmat : Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hact : Continuous (fun g : HA R σ J => g • ratTup (F := F) R X) := by
    refine continuous_pi fun b => ?_
    show Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec
        (ratTup (F := F) R X b))
    exact hmat.matrix_mulVec continuous_const
  exact isClosed_eq hact continuous_const

end Gen

theorem admissible_tuple_holds : AdTup := by
  intro F E _ _ _ _ _ σ n J hCM hJ
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hmI : Measurable (haMap σ J (fstA F)) :=
    (PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (fstA F)
      (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (fstA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_fstA)).measurable
  have hmF : Measurable (haMap σ J (sndA F)) :=
    (PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (sndA F)
      (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (sndA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_sndA)).measurable
  have : SecondCountableTopology (HA (Ainf F) σ J) :=
    PI.VolStabS.TopoAF.secondCountable_HA_of (Ainf F) σ J
  have : SecondCountableTopology (HA (Af F) σ J) :=
    PI.VolStabS.TopoAF.secondCountable_HA_of (Af F) σ J
  have : SigmaCompactSpace (HA (Ainf F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaCompactSpace (HA (Af F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsub : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
      [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] (r : ℕ) (P : Frame E n r)
      (μ : Measure (Hsub R σ J P)), μ.IsHaarMeasure → SFinite (amb μ) := by
    intro R _ _ _ _ _ _ _ r P μ hμ
    have : SecondCountableTopology (HA R σ J) := PI.VolStabS.TopoAF.secondCountable_HA_of R σ J
    have hcl : IsClosed (Hsub R σ J P : Set (HA R σ J)) := isClosed_stabT σ J R (tupH P)
    have : LocallyCompactSpace (Hsub R σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology (Hsub R σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have : SigmaCompactSpace (Hsub R σ J P) := sigmaCompactSpace_of_locallyCompact_secondCountable
    have := hμ
    infer_instance
  refine ⟨hmI.prodMk hmF, fun g₁ g₂ => ⟨PI.UnitaryGroupMassFormula.MeasWCore.haPair σ J g₁ g₂,
      PI.UnitaryGroupMassFormula.MeasWCore.splitA_haPair σ J g₁ g₂⟩, ?_, ?_, ?_, fun g => (continuous_const_mul g).measurable,
    fun g => (continuous_const_mul g).measurable, fun μ hμ => by have := hμ; infer_instance,
    fun μ hμ => by have := hμ; infer_instance, fun r P μ hμ => hsub (Ainf F) r P μ hμ,
    fun r P μ hμ => hsub (Af F) r P μ hμ, ?_, ?_⟩
  · intro a g X
    constructor
    · funext x i
      change tensMap (E := E) (fstA F)
          (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) =
        ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
          (tensMap (E := E) (fstA F))).mulVec (fun j => tensMap (E := E) (fstA F) (X x j))) i
      rw [RingHom.map_mulVec]
      rfl
    · funext x i
      change tensMap (E := E) (sndA F)
          (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) =
        ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
          (tensMap (E := E) (sndA F))).mulVec (fun j => tensMap (E := E) (sndA F) (X x j))) i
      rw [RingHom.map_mulVec]
      rfl
  · intro a X0
    exact ⟨funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (fstA F) (X0 x i),
      funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (sndA F) (X0 x i)⟩
  · intro a X Y h1 h2
    funext x i
    have e : PI.UnitaryGroupMassFormula.MeasWCore.splT (X x i) = PI.UnitaryGroupMassFormula.MeasWCore.splT (Y x i) :=
      Prod.ext (congrFun (congrFun h1 x) i) (congrFun (congrFun h2 x) i)
    have := congrArg PI.UnitaryGroupMassFormula.MeasWCore.splInv e
    rwa [PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT, PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT] at this
  · rintro Λ ⟨L, hL, rfl⟩
    exact (isClosed_kf σ J L hL.fg).measurableSet
  · rintro Λ μf ⟨L, hL, rfl⟩ hμf hpos hfin r P μ hμ
    have : T2Space (Af F ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Af F)
    obtain ⟨hKc, hKo⟩ := compact_open_of_haar_pos_finite _ (isClosed_kf σ J L hL.fg) μf hpos hfin
    have hcl : IsClosed (Hsub (Af F) σ J P : Set (HA (Af F) σ J)) := isClosed_stabT σ J (Af F) (tupH P)
    have := hμ
    refine ⟨hKo.preimage continuous_subtype_val |>.measure_pos μ ⟨1, (Kf σ J _).one_mem⟩, ?_⟩
    exact (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top

end Formalism.L2.SG.Pf.NcS.AdTupPf
