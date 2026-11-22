module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGL
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  first | exact @GlobalTheory.DiagUnifFactor.main | exact GlobalTheory.DiagUnifFactor.main | (intros; apply GlobalTheory.DiagUnifFactor.main <;> assumption)
