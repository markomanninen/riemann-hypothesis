module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdBideterminantsEqColumnChoiceMinorProduct
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
theorem _root_.GlobalTheory.T.prod_bideterminants_eq_columnChoice_minorProduct : ∀ (D : D7) (K : Type) [CommRing K] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (ν : D.what₂.Tau → Fin N → ℕ), NuFits D nu ν → ∀ g : D.what₂.Tau → Matrix (Fin N) (Fin N) K → K,
    (∀ τ, g τ ∈ bideterminantFunctionsOfShape K N (ν τ)) → ∃ J : KM.ColChoice N nu, ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) K,
      ∏ τ, g τ (y τ) = GL3Columns.minY N nu J (fun s => GL3Columns.colsOf (y (tauPl D s))) := by
  first | exact @GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY | exact GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY | (intros; apply GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY <;> assumption)
