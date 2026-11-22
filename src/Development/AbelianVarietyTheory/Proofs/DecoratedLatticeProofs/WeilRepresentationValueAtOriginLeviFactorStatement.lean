module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

namespace I195MixedCoordinates_34c45ee3f9864caed77cce75

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

end I195MixedCoordinates_34c45ee3f9864caed77cce75

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) ((_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (f) 0 := by
  first | exact @GlobalTheory.LeviOrigin.value_at_origin | exact GlobalTheory.LeviOrigin.value_at_origin | (intros; apply GlobalTheory.LeviOrigin.value_at_origin <;> assumption)
