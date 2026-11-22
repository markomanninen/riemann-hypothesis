module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixesMaximalUnramifiedExtensionQl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_maximalUnramifiedExtension_Ql : ∀ (l : ℕ) [Fact l.Prime] (g : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x := by
  first | exact @GlobalTheory.InertQlUnr.IK_qlExt_fixes_Kur | exact GlobalTheory.InertQlUnr.IK_qlExt_fixes_Kur | (intros; apply GlobalTheory.InertQlUnr.IK_qlExt_fixes_Kur <;> assumption)
