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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FinFib

section Generic

variable {G : Type} [Group G]

def twR (θ : G →* G) (x y : G) : Prop := ∃ g, y = g⁻¹ * x * θ g

theorem twR_equiv (θ : G →* G) : Equivalence (twR θ) := by
  constructor
  · intro x
    exact ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk (twR θ) x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ twR θ x y :=
  ⟨fun h => (twR_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locEl_eventually_mem (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  filter_upwards [UnitStable.eventually_mem_KGL δ, UnitStable.eventually_mem_KGL (δ * thE E n δ)] with w h1 h2
  unfold locEl
  split_ifs
  · exact h2
  · exact h1

end GlobalTheory.BCT.FinFib

namespace GlobalTheory.BCT.FinFib

end GlobalTheory.BCT.FinFib
