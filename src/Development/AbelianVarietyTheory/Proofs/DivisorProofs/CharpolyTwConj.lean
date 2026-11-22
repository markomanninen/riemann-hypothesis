module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBoundedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGLStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizerStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo
public import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PLocDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomialsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FibStable

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun x => ⟨1, by simp⟩, fun ⟨g, h⟩ => ⟨g⁻¹, by rw [h, map_inv]; group⟩,
    fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨g * k, by rw [h', h, map_mul]; group⟩⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

theorem rep_cls (θ : G →* G) (y : G) : ∃ g, (cls θ y).rep = g⁻¹ * y * θ g :=
  (cls_eq_iff θ _ _).1 (cls_rep θ (cls θ y)).symm

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [nrmL_twConj, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

end Local

end GlobalTheory.BCT.FibStable
