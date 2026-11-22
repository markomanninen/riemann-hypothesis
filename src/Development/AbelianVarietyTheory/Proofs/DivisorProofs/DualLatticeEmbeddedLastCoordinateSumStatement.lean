module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.StatementLA
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Formalism.LocalToGlobal.Divisibility.BrJoint
public import Formalism.LocalToGlobal.Columns.CoefficientsModP
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  first | exact @GlobalTheory.dualFr_tauLat_sumLat | exact GlobalTheory.dualFr_tauLat_sumLat | (intros; apply GlobalTheory.dualFr_tauLat_sumLat <;> assumption)
