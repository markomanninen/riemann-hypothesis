module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

@[expose] public section

open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_iff_irreducible : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
