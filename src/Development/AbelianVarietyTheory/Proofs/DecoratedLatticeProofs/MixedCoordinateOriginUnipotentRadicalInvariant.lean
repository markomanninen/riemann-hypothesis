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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement

namespace I195MixedCoordinates_069c5864e5661f762e792771

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

end I195MixedCoordinates_069c5864e5661f762e792771

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnipZero

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    first | exact symplOH_zero_right .. | simp [symplOH] | (rw [symplOH]; simp)
  simp [heisO, h]

theorem mixS_zero_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ b, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ c, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hW μ 𝓕 hμ f hf
  rcases Nat.eq_zero_or_pos ρ with hρ | hρ
  · subst hρ
    obtain ⟨-, -, h0⟩ := GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ
    obtain ⟨-, hB, hC⟩ := h0 S S₀ d
    refine ⟨fun b => ?_, fun c => ?_⟩
    · rw [hB b, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]; rfl
    · rw [hC c, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]; rfl
  · obtain ⟨hiso, hrat, -, -, -, hres, -, hnB, hnC⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hrat]; exact hμ
    have key : ∀ n : NI S d.e, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om ((n : GA D S), 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 f 0 := by
      intro n
      change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 (om ((n : GA D S), 1) f) 0 = I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0
      rw [hres, hres, map_zero, heisO_zero, heisO_zero]
      exact GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D S S₀ T ρ d.e d.i₀ (hiso hρ) ψ χS χT om hW μ 𝓕 hμ' n f hf
    exact ⟨fun b => key ⟨_, hnB b⟩, fun c => key ⟨_, hnC c⟩⟩

end GlobalTheory.UnipZero
