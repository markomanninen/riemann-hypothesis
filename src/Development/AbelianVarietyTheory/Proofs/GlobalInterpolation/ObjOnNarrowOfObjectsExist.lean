module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.FewBadPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill

@[expose] public section

noncomputable section

namespace GlobalTheory.ObjExCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

variable {R : Ranks}

theorem one_lt_condE (H : Host R) : 1 < condE H := by
  unfold condE
  exact lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem norm_modEq (H : Host R) (π : 𝓞 H.E) {T N : ℕ} (hN : N ≠ 0)
    (hn : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h1 : π - 1 ∈ Ideal.span {((N : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD N] := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hyi : IsIntegral ℤ (a : H.E) := RingOfIntegers.isIntegral_coe a
  have hπ : (π : H.E) = 1 + N * (a : H.E) := by
    have := congrArg (fun z : 𝓞 H.E => (z : H.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    linear_combination -this
  have hci : IsIntegral ℤ (H.conj (a : H.E)) := hyi.map ((H.conj : H.E →+* H.E).toIntAlgHom)
  rw [hπ, map_add (f := _), map_mul, map_one, map_natCast] at hn
  set z : H.E := a + H.conj (a : H.E) + N * (a * H.conj (a : H.E)) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := H.E) N).mul (hyi.mul hci))
  have hM0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have h4 : z = algebraMap ℚ H.E (((T : ℚ) - 1) / N) := by
    have hM0' : (N : H.E) ≠ 0 := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff ] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((T : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℚ) = ((N * n : ℤ) : ℚ) := by
    have : (n : ℚ) = ((T : ℚ) - 1) / N := by simpa using hn'
    push_cast
    rw [this]
    field_simp
  exact (Nat.modEq_iff_dvd.2 ⟨n, by exact_mod_cast h5⟩).symm

theorem T_modEq (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD condE D.host] := by
  obtain ⟨π, -, h2, h3⟩ := D.T_norm u
  have h0 : condE D.host * (D.host.g 0 * D.host.g 1) ^ 2 ≠ 0 :=
    Nat.mul_ne_zero (by have := one_lt_condE D.host; omega)
      (pow_ne_zero _ (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact (norm_modEq D.host π h0 h2 h3).of_mul_right _

end GlobalTheory.ObjExCompare

end
