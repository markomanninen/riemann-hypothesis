module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterParahoricCosetsEqSchurCount
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Formalism.LocalToGlobal.Columns.HeckeSp

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (GlobalTheory.GLDoubling.torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, InSupp x → (R.filter fun j => InSupp (((j * GlobalTheory.ZonalCellDecomposition.mtor ϖ (indic s))⁻¹).1 * x)).card = (RK.filter fun g => ∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]).card := by
  exact @GlobalTheory.ParHeckeTarget.card_filter_eq
