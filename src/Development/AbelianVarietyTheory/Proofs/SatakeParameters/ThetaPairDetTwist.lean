module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralIntegrable
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulReStatement

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

section Mat

variable {α β : Type} [Fintype α]


open MeasureTheory ValuativeRel in
open scoped TensorProduct Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GodementJacquet.parab_mul_eMat
    (p : _root_.GlobalTheory.SmGL.parab k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t)))) :
    (p : GL (Fin (r + t)) k).val * _root_.GlobalTheory.GodementJacquet.eMat k r t =
      _root_.GlobalTheory.GodementJacquet.eMat k r t * (_root_.GlobalTheory.SmGL.leviProj k
        (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
          GL (Fin r) k).val := by
  have hE : ∀ (i : Fin (r + t)) (j : Fin r),
      _root_.GlobalTheory.GodementJacquet.eMat k r t i j = if i = Fin.castAdd t j then 1 else 0 := by
    intro i j
    simp [_root_.GlobalTheory.GodementJacquet.eMat, Fin.ext_iff]
  have hlow : ∀ (i : Fin t) (j : Fin r),
      (p : GL (Fin (r + t)) k).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
    intro i j
    have := (_root_.GlobalTheory.SmGL.mem_parab_two k).1 p.2 i j
    simpa [_root_.GlobalTheory.SmGL.stdSum] using this
  have hL : ∀ (i j : Fin r), (_root_.GlobalTheory.SmGL.leviProj k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
        GL (Fin r) k).val i j = (p : GL (Fin (r + t)) k).val (Fin.castAdd t i) (Fin.castAdd t j) := by
    intro i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply]
    rfl
  ext i j
  simp only [Matrix.mul_apply, hE, hL, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [eq_comm]
  · rw [hlow]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    rw [if_neg]
    simp only [Fin.ext_iff, Fin.coe_natAdd, Fin.coe_castAdd]
    omega

end Mat

section Coef

variable {σ : Representation ℂ (GL (Fin r) k) V} {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

end Coef

section Law

end Law

section Int

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

variable (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
include hσ hs hp hu





end Int

section Family

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}


variable [m.IsMulLeftInvariant] (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
      Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)



end Family

section Abstract

variable {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

end Abstract

section Pairing

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)


end Pairing

section NonVanishing

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsOpenPosMeasure] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

end NonVanishing

end GlobalTheory.GodementJacquet

