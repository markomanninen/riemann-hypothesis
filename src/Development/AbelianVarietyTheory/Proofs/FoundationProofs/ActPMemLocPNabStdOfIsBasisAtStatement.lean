module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  first | exact @GlobalTheory.NabStab.polyAction_mem_locP_nabStd | exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd | (intros; apply GlobalTheory.NabStab.polyAction_mem_locP_nabStd <;> assumption)
