module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI

@[expose] public section

noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
