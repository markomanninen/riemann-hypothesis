module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  first | exact @GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE | exact GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE | (intros; apply GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE <;> assumption)
