module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idem_smul_mul {A : Type} [CommRing A] [Algebra (AF F) A] {ε : AF F} (hε : ε * ε = ε) (a b : A) :
    (ε • a + (1 - ε) • (1 : A)) * (ε • b + (1 - ε) • (1 : A)) = ε • (a * b) + (1 - ε) • (1 : A) := by
  simp only [Algebra.smul_def, mul_one]
  have he : algebraMap (AF F) A ε * algebraMap (AF F) A ε = algebraMap (AF F) A ε := by rw [← map_mul, hε]
  rw [map_sub, map_one]
  linear_combination (a * b - a - b + 1) * he


variable (E) in
def idemUnit (ε : AF F) (hε : ε * ε = ε) : (AE F E)ˣ →* (AE F E)ˣ where
  toFun l := ⟨ε • l.1 + (1 - ε) • 1, ε • (l⁻¹ : (AE F E)ˣ).1 + (1 - ε) • 1,
    by rw [idem_smul_mul hε, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul],
    by rw [idem_smul_mul hε, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩
  map_one' := Units.ext (by simp only [Units.val_one, Units.val_mk]; rw [← add_smul, add_sub_cancel, one_smul])
  map_mul' a b := Units.ext (by simp only [Units.val_mul, Units.val_mk]; rw [idem_smul_mul hε])


def eFin (v : Pl F) : AF F := GlobalTheory.LatVac.liftV v 1

def eInf (F : Type) [Field F] [NumberField F] : AF F := realAd F 1

theorem eFin_idem (v : Pl F) : eFin v * eFin v = eFin v := by
  have h := GlobalTheory.LatVac.at_liftV v 1 (eFin v - 1) (by
    rw [eFin, map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem eInf_idem : eInf F * eInf F = eInf F := by
  have h := at_partInf (M := AF F) (1 : AF F) (eInf F - 1) (by
    rw [eInf, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  simp only [partInf, smul_eq_mul, mul_one] at h
  unfold eInf at h ⊢
  rw [sub_mul, one_mul, sub_eq_zero] at h
  exact h


variable (E) in
def unitAt (v : Pl F) : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eFin v) (eFin_idem v)


variable (F E) in
def unitArch : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eInf F) eInf_idem



theorem unitAt_mem (v : Pl F) (l : (AE F E)ˣ) : unitAt E v l ∈ idelesAt E (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  change u • (eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1) = 0
  rw [show eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1 = eFin v • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem unitArch_mem (l : (AE F E)ˣ) : unitArch F E l ∈ idelesAt E (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  change u • (eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1) = 0
  rw [show eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1 = eInf F • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

end GlobalTheory.ThK.ConeEuler
