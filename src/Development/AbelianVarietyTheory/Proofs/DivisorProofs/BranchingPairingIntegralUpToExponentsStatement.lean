module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponents
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
theorem _root_.GlobalTheory.T.branchingPairing_integral_upToExponents : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsFullLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  first
  | exact GlobalTheory.BrPairLocal.finLocal emb hN Λ σ hI hS M L hM hL w u v hu hv
  | exact GlobalTheory.BrPairLocal.finLocal emb hN Λ σ hI hS M L hM.toIsLattice hL w u v hu hv
