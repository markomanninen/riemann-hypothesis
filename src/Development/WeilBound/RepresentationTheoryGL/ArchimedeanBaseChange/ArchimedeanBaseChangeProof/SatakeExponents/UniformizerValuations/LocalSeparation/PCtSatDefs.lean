module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSuStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev tJ {w : Pl E} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (m i : ℕ) : GLw m w :=
  GlobalTheory.WeylGL.tor h0 fun r : Fin m => if (r : ℕ) < i then 1 else 0

abbrev pairsK (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter fun p => p.1 + p.2 = k

end PositivityTheory.Rg.BcB.F.RS
