module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay.Model

variable {D : D7}

theorem isCuspFun_zero (V : HSp D) : IsCuspFun V fun _ => 0 := fun _ _ _ _ _ _ _ _ => by simp

def line (D : D7) : HSp D := Examples₂.posSpace Examples₂.star_isIntegral 1

def plane (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 2 ![false, true] 1 1

theorem isIsoFrame_plane (D : D7) : IsIsoFrame (plane D) (r := 1) (Matrix.of fun _ _ => 1) := by
  refine ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrFun h (0 : Fin 2)
    exact one_ne_zero this
  · have hg : ∀ i j : Fin 2, (plane D).gram i j = if i = j then (Examples₂.sgn (![false, true] i) : D.host.E) else 0 :=
      Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 2 ![false, true] 1 1
    funext a b
    change ∑ j : Fin 2, (∑ i : Fin 2, D.sp.cm.sig 1 * (plane D).gram i j) * 1 = 0
    simp [Fin.sum_univ_two, hg, Examples₂.sgn]

theorem isClosed_NI (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) :
    IsClosed (NI V C : Set (GA D V)) := by
  obtain ⟨L, hL, -⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm V C hC.2.1 hC.2.2
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : T2Space (AF D.host.F ⊗[D.host.F] D.host.E) :=
    .of_injective_continuous (f := (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun.toLinearMap)
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  rw [GlobalTheory.AutFunCompare.NI_eq]
  have hcl : IsClosed {g : GA D V |
      ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) * (C * L).map (inclR (F := D.host.F) (AF D.host.F)) = 0 ∧
      (1 - (C * L).map (inclR (F := D.host.F) (AF D.host.F))) * ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) *
        (1 - GlobalTheory.AutFunCompare.adj D.sp.cm V ((C * L).map (inclR (F := D.host.F) (AF D.host.F)))) = 0} :=
    (isClosed_eq ((hm.sub continuous_const).matrix_mul continuous_const) continuous_const).inter
    (isClosed_eq ((continuous_const.matrix_mul (hm.sub continuous_const)).matrix_mul continuous_const) continuous_const)
  convert hcl using 1
  exact Set.ext fun g => GlobalTheory.AutFunCompare.mem_unipRad_idem D.sp.cm V C L hL g

theorem not_isCuspFun_const (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    {c : ℂ} (hc : c ≠ 0) : ¬ IsCuspFun V fun _ => c := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have : LocallyCompactSpace (NI V C) := (isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : DiscreteTopology (NIQ V C) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ : Measure (NI V C) := Measure.haar
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ V C) μ
  have h0 := h r C hC μ 𝓕 inferInstance h𝓕 1
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hint : IntegrableOn (fun _ : NI V C => c) 𝓕 μ := by
    have key : ∀ N : Subgroup (GA D V), N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => c) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => c) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) μ 𝓕 inferInstance h𝓕
  have hlt : μ 𝓕 ≠ ⊤ := by
    rcases (integrableOn_const_iff (C := c)).1 hint with h | h
    · exact absurd (by simpa using h) hc
    · exact h.ne
  rw [setIntegral_const, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact ENNReal.toReal_ne_zero.2 ⟨hne, hlt⟩ h0
  · exact hc h0

theorem not_isCuspFun_one_plane (D : D7) : ¬ IsCuspFun (plane D) fun _ => 1 :=
  not_isCuspFun_const _ (isIsoFrame_plane D) one_ne_zero

end GlobalTheory.CuspDecay.Model

end
