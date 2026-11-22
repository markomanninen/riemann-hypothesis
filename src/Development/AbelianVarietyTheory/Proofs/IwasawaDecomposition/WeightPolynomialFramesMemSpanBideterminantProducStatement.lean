module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightPolynomialFramesMemSpanBideterminantProduc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BideterminantFunctionsOfShape

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPolynomial_frames_mem_span_bideterminantProducts : ∀ (K L : Type) [Field K] [Field L] [Infinite K] (φ : K →+* L) (ι : Type) [Fintype ι] (N : ℕ)
    (ν : ι → Fin N → ℕ) (M : ι → Matrix (Fin N) (Fin N) L), ∀ Q ∈ WtPol K ν,
    (fun y : ι → Matrix (Fin N) (Fin N) L =>
      MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ Q)) ∈
    Submodule.span L {F | ∃ g : ι → Matrix (Fin N) (Fin N) L → L, (∀ τ, g τ ∈ bideterminantFunctionsOfShape L N (ν τ)) ∧
      F = fun y => ∏ τ, g τ (y τ)} := by
  first | exact @GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts | exact GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts | (intros; apply GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts <;> assumption)
