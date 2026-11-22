module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacterStatement

namespace I195MixedCoordinates_d909b66b3061dc587285daac

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

end I195MixedCoordinates_d909b66b3061dc587285daac

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ValueAtOrigin

theorem mixS_zero_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ h f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source d) T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) ((_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source d) T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hS hS₀ μ 𝓕 hμ h f hf
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · have hz := (GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d μ 𝓕 hμ
    have hi := (GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hS.std).2.2.2 χS χT om om₀ hS hS₀ 1 h f hf
    change I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f 0)
    rw [hz, hz, hi, map_one]
  · obtain ⟨hsp, hrat, -, -, -, hmix, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    have hc := GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT χT om om₀ hS hS₀ μ 𝓕 (hrat ▸ hμ) h f hf
    have h0 : ∀ g : WO S T → ℂ, heisO ψ S T (d.extX T 0) g = g := by
      intro g; funext w
      simp [heisO, symplOH_zero_right]
    change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0)
    rw [hmix, hmix, h0, h0, hc]

end GlobalTheory.ValueAtOrigin
