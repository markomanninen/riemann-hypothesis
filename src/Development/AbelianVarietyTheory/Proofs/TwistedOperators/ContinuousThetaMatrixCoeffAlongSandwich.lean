module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaCoefCont

private theorem measure_fundamentalDomain_ratL_lt_infty {D : D7} (V W : HSp D) (ν : Measure (WO V W)) (𝓕 : Set (WO V W))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) : ν 𝓕 < ⊤ := by
  obtain ⟨hg, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI := hg
  haveI := hsc
  haveI := hdisc
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov ν h𝓕

theorem continuous_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  intro D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hfin : ν 𝓕 < ⊤ := measure_fundamentalDomain_ratL_lt_infty V W ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C', hC'⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG'
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hE : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
    unfold GlobalTheory.IsoMean.emb
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  rw [continuous_iff_continuousAt]
  intro y₀
  haveI : SecondCountableTopology (Mx D a b) := (GlobalTheory.MixModel.lattice_Mx D a b).2.2.1
  haveI : FirstCountableTopology (Mx D a b) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C * C') ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_id continuous_const))).mul
        (hG.cont.comp (continuous_id.add continuous_const))).mul
        (continuous_star.comp hG'.cont)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star, heisO, norm_mul, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg (G u)).trans (hC u))
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_const hE))).mul
      (hG.cont.comp (continuous_const.add hE))).mul continuous_const).continuousAt

end GlobalTheory.ThetaCoefCont

end
