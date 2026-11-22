module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

noncomputable section

open scoped ComplexConjugate NNReal ENNReal
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp GlobalTheory.MixModel
open GlobalTheory.Mem.Th (InfF CptF)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause DoublingIso)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP.Model

variable {D : D7} {A B : HSp D}

theorem vol_pos (mH : Measure (GA D B)) [mH.IsHaarMeasure] : 0 < (autMeasure B mH).real Set.univ :=
  ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 (NeZero.ne _)) (measure_ne_top _ _)

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)}

end GlobalTheory.RallisIP.Model

end
