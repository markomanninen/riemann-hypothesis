module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

variable {n : Type} [Fintype n] [DecidableEq n]

def tU : P.R.Bˣ := (isUnit_tB P).unit

theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

end GlobalTheory.PMon.Model

end
