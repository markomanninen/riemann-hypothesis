module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.RationalSubgroupFund

theorem countable_discrete_exists_fundamentalDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  intro D W Γ hΓ
  obtain ⟨_, h2, _, h4, h5, h6, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := h2; haveI := h4; haveI := h5; haveI := h6
  haveI hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨(x : GA D W), hΓ x.2⟩ : GQ W))
      (continuous_subtype_val.subtype_mk _)
      (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
  obtain ⟨hc, 𝓓, h𝓓m, h𝓓⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  haveI := hc
  refine ⟨hc, hdisc, fun μ _ => ⟨𝓓, ?_⟩⟩
  exact IsFundamentalDomain.mk' h𝓓m.nullMeasurableSet (fun g => h𝓓 g)

end GlobalTheory.RationalSubgroupFund
