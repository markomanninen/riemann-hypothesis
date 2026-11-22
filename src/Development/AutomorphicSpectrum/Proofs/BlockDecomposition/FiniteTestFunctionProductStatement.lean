module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProduct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_test_function_product : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b), finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | exact GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | (intros; apply GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor <;> assumption)
