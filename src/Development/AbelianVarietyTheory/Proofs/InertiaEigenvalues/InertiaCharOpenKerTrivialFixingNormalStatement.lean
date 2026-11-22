module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormal
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
theorem _root_.GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  first | exact @GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | exact GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | (intros; apply GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal <;> assumption)
