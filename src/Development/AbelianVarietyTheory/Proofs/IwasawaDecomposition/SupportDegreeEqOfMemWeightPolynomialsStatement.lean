module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomials
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_degree_eq_of_mem_weightPolynomials : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  first | exact @GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | exact GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | (intros; apply GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol <;> assumption)
