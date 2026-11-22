module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

@[expose] public section

noncomputable section

namespace GlobalTheory.RamValCheck

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem g_coprime (D : Formalism.BasicNotions.D7) (k : Fin 2) (p : ℕ)
    (hp : p ∈ D.host.condN.primeFactors) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hdvd : p ∣ D.host.QS * D.host.q * D.host.d := Nat.dvd_of_mem_primeFactors hp
  refine Nat.Coprime.coprime_dvd_right hdvd ?_
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

end GlobalTheory.RamValCheck
