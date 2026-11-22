module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL)
      (Pl : LocPrime l) (AI : LocAinf l Pl), GlobalTheory.Per.IsStd Pl AI →
      ∃ β : TW (GlobalTheory.BKReal.OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B,
        (∀ x : ↥T.L.T,
          β ((1 : GlobalTheory.BKReal.OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) =
            (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧
        (∀ g b, β (GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g b) =
          actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧
        (∀ b, β (TWmap (GlobalTheory.BKReal.frobOB l ↥(OL LL)) T b) =
          φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧
        ∀ c ∈ continuousCocycles T.ρ,
          c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔
            ∃ b, GlobalTheory.BKGal.IsCobOf (GlobalTheory.BKGal.sQ l) T b c := by
  exact @GlobalTheory.BKGal.CrisTensor.exists_equiv
