module

public import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
public import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
public import Formalism.LocalToGlobal.GlobalTheory.GL3.ThirdClauseIntegralCombination
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

namespace JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Good

variable {p : ℕ} [Fact p.Prime] {σ ι : Type*}

variable (δ : ι → MvPowerSeries σ ℂ_[p] →+ MvPowerSeries σ ℂ_[p])

def Wd (l : List ι) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  l.foldr (fun j H => δ j H) G

def Good (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ l : List ι, IsIntP (MvPowerSeries.constantCoeff (Wd δ l G))

variable {δ}

end Good

section Ring

variable {p : ℕ} [Fact p.Prime]

end Ring

section Deriv

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

end Deriv

section Chain

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Chain

section Lin

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom

theorem isPadicIntegral_lamC_K (c : 𝓞 D.host.K) : IsIntP (lamC lam (D.host.φ₀ ((c : D.host.K) : D.host.E))) := by
  have hI : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
    map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat _)]
  exact RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)

variable (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Lin

section Core

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end Core

section Log

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime]

end Log

end JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

end Formalism.L2.KerInert
