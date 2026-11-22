module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRoot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l → x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  first | exact @GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | exact GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | (intros; apply GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup <;> assumption)
