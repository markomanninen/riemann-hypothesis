module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpan
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.WeylLatDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEmbeddingMatrixSubstitution_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  first | exact @GlobalTheory.IntegralityCompare.twSub_mem_ratSpan | exact GlobalTheory.IntegralityCompare.twSub_mem_ratSpan | (intros; apply GlobalTheory.IntegralityCompare.twSub_mem_ratSpan <;> assumption)
