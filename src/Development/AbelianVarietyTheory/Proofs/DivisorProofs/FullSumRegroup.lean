module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MkEqIffRelAndOutRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkIffOfRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBijStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulIntStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjByCarryingUnitMemPositiveSimilitudeFormGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjOfRelSimilitudePairsSameFormStatement

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dite_eq_left h]⟩

end GlobalTheory.LKCx.Regroup
