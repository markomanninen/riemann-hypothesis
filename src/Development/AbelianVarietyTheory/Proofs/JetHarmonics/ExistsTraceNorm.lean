module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

end GlobalTheory.PlaceComponents
