module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProductsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandraStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMassLowerBoundOfOrthonormalLatticeFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftScalarOfInnerProductFormulaBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialLStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLawStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValueStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowAdel

theorem deltaNorm_all (D : D7) : DeltaNorm D := by
  intro i σ
  have h := GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ)
    (fun ρ => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.2.1.le)
    (fun ρ => by
      obtain ⟨-, -, hpq, hWV⟩ := GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ
      exact ⟨by omega, by omega⟩)
    (fun ρ => ⟨(GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).1, (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.1⟩)
  simpa [deltaAtEmb] using h

end GlobalTheory.LowRowAdel
