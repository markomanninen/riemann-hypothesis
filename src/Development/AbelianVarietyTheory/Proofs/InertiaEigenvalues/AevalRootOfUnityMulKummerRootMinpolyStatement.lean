module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpoly
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  first | exact @GlobalTheory.MinpolyKummerUr.aeval_mul_root | exact GlobalTheory.MinpolyKummerUr.aeval_mul_root | (intros; apply GlobalTheory.MinpolyKummerUr.aeval_mul_root <;> assumption)
