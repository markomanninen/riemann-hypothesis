module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

namespace I195MixedCoordinates_0bc2bf51bedd9bcbcf543475

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

end I195MixedCoordinates_0bc2bf51bedd9bcbcf543475

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ x a, (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) f) x = (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 f (x + a)) ∧ (∀ x a, (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extY T a) f) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 f x) ∧ (∀ x w, (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) x = heisO ψ S₀ T w ((_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 f x)) ∧ (Continuous fun p : Mx D T.rank ρ × WO S₀ T => (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 f p.1 p.2) ∧ ∀ w, HasSum (fun x : Matrix (Fin T.rank) (Fin ρ) D.host.E => (_root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source d) T ψ v.μ v.𝓕 f (rat x) w) (f (d.ext0 T w)) := by
  first | exact @GlobalTheory.HeisMixSource.heis_mixS | exact GlobalTheory.HeisMixSource.heis_mixS | (intros; apply GlobalTheory.HeisMixSource.heis_mixS <;> assumption)
