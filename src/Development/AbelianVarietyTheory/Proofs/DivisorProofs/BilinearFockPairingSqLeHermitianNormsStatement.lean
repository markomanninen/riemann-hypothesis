module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinearFockPairingSqLeHermitianNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.StatementLA
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  first | exact @GlobalTheory.FockCauchySchwarz.pairBK_sq_le | exact GlobalTheory.FockCauchySchwarz.pairBK_sq_le | (intros; apply GlobalTheory.FockCauchySchwarz.pairBK_sq_le <;> assumption)
