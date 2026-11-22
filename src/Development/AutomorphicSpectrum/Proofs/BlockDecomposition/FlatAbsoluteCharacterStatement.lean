module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ), FlatFn (absFn (E := E) N w) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_flat | exact GlobalTheory.CompanionTheory.LimV.absFn_flat | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_flat <;> assumption)
