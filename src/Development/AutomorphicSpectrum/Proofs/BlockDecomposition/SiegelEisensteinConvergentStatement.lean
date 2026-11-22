module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

@[expose] public section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_convergent : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  first | exact @GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | exact GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | (intros; apply GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law <;> assumption)
