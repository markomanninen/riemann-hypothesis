module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie

namespace I195MixedCoordinates_052755a8a20ae3f544412ebb

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_052755a8a20ae3f544412ebb

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixValues

theorem mixS_theta (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) :
    IsThetaFunO ψ S₀ T ((_root_.I195MixedCoordinates_052755a8a20ae3f544412ebb.source d) T ψ μ 𝓕 f x) := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · change IsThetaFunO ψ S₀ T (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f x)
    rw [(GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d μ 𝓕 hμ f x]
    exact ((GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hψ).2.2.1 f).2 hf
  · obtain ⟨hiso, hrat, -, -, -, hres, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    change IsThetaFunO ψ S₀ T (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f x)
    rw [hres]
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hrat]; exact hμ
    have hg := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 (d.extX T x) f hf
    exact ((GlobalTheory.TowerRestrict.res_theta D S S₀ T ρ d.e d.i₀ (hiso hρ) ψ hψ μ 𝓕 hμ').1 _ hg).2.1

end GlobalTheory.MixValues

theorem GlobalTheory.MixValues.mixed_values : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D := by
  intro D ψ hψ
  refine ⟨fun S S₀ T ρ d μ 𝓕 hμ f hf x => GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ f hf x, ?_⟩
  intro S T T₀ ρ d μ 𝓕 hμ f hf y
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hcd := GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ
  have h1 : IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) := ((hcd S T).2.2.1 f).2 hf
  have h2 := GlobalTheory.MixValues.mixS_theta D ψ hψ T T₀ S ρ d μ' 𝓕' hμ' _ h1 (incA D D.host.xi0⁻¹ • y)
  change IsThetaFunO ψ T₀ S (I195MixedCoordinates_79cab7195843a34bfe21655d.source d S ψ μ' 𝓕' _ (incA D D.host.xi0⁻¹ • y)) at h2
  rw [hsw] at h2
  exact ((hcd S T₀).2.2.1 _).1 h2
