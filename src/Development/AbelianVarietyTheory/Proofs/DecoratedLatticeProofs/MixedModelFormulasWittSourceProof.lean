module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPointStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulasStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariantStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixSourceFormulas

theorem mixed_source : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  intro D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ f hf
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ ho.std S T).1
  have hbr : ∀ (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 :=
    fun f x => (GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 f x
  have hmv := GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hun := GlobalTheory.T.wittMixedModel_unipotent_formulas D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hlv := fun w => GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ (heisO ψ S T w f) (hth w f hf)
  unfold I195MixedCoordinates_3601ff04f10fcda6f28caf89.source at hmv
  unfold I195MixedCoordinates_34c45ee3f9864caed77cce75.source at hlv
  unfold HypDec.mixS HypDec.extX HypDec.extY HypDec.ext0 at hbr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    have hor := GlobalTheory.T.mixedCoordinate_origin_weilRep_target_equivariant D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ h (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f) (hth _ f hf)
    unfold I195MixedCoordinates_6a77e1566d048881366221d8.source at hor
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [(hmv x).1 h, hor]
    exact congrArg (om₀ (1, h)) (hbr f (mt T h⁻¹ ⬝ x)).symm
  · intro g x
    have e := (hmv x).2.1 1 g
    rw [map_one, one_mul, Units.val_one, Matrix.mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).1 g]
    exact congrArg (om₀ (g, 1)) (hbr f x).symm
  · intro a x
    have e := (hmv x).2.1 a 1
    rw [map_one, mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).2.2 a]
    exact congrArg (fun (z : WO S₀ T → ℂ) => (((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • z) (hbr f (x ⬝ a.1)).symm
  · intro b x
    exact (hun x).1 b
  · intro c x
    exact (hun x).2 c

end GlobalTheory.MixSourceFormulas
