module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
      [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
      [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
      (T : LocLat (GlobalTheory.BKGal.Gl l) ℚ_[l] K O) (g : GlobalTheory.BKGal.Gl l)
      (C : GlobalTheory.MemLoc.Core l),
      ∀ v ∈ Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
        ∃ (β : Per.Bcris l) (x : ↥T.L.T),
          C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x},
        GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g v ∈
          Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
            ∃ (β : Per.Bcris l) (x : ↥T.L.T),
              C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  exact @GlobalTheory.BKGal.FilStable.fil_zero_stable
