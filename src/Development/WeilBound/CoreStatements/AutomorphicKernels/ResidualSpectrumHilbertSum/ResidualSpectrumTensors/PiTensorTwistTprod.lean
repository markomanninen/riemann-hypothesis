module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LocalComponentTwist

theorem modExp_const {a d : ℕ} (i : Fin d) :
    modExp (fun _ : Fin d => Fin a) i = (a : ℤ) * ((d : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) := by
  have e : modExp (fun _ : Fin d => Fin a) i =
      (∑ _b ∈ Finset.Ioi i, (a : ℤ)) - ∑ _b ∈ Finset.Iio i, (a : ℤ) := by
    unfold modExp
    congr 1
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
  have hi := i.2
  have hc : ((d - 1 - (i : ℕ) : ℕ) : ℤ) = (d : ℤ) - 1 - ((i : ℕ) : ℤ) := by omega
  rw [e, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul, hc]
  ring

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a d : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem piTensor_twist_tprod (ρ : Representation ℂ (GL (Fin a) k) V) (χ : Fin d → GL (Fin a) k →* ℂˣ)
    (g : Fin d → GL (Fin a) k) (x : Fin d → V) :
    piTensor (fun i => GlobalTheory.SmGL.twist ρ (χ i)) g (PiTensorProduct.tprod ℂ x) =
      ((∏ i, χ i (g i) : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ fun i => ρ (g i) (x i) := by
  rw [piTensor_tprod, Units.coe_prod]
  exact (PiTensorProduct.tprod ℂ).map_smul_univ (fun i => ((χ i (g i) : ℂˣ) : ℂ)) fun i => ρ (g i) (x i)

theorem levi_eq (ρ : Representation ℂ (GL (Fin a) k) V) (s t : Fin d → ℂ)
    (hst : ∀ i, t i = ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + s i) :
    piTensor (fun i => GlobalTheory.SmGL.twist ρ (detChar (Fin a) (absPow k (s i)))) =
      GlobalTheory.SmGL.twist (piTensor fun i => GlobalTheory.SmGL.twist ρ (detChar (Fin a) (absPow k (t i))))
        (deltaHalf k fun _ : Fin d => Fin a)⁻¹ := by
  refine MonoidHom.ext fun g => ?_
  have key : (deltaHalf k fun _ : Fin d => Fin a)⁻¹ g * ∏ i, detChar (Fin a) (absPow k (t i)) (g i) =
      ∏ i, detChar (Fin a) (absPow k (s i)) (g i) := by
    rw [MonoidHom.inv_apply, deltaHalf_apply, inv_mul_eq_iff_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [detChar_apply, detChar_apply, hst i, absPow_add, MonoidHom.mul_apply]
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, GlobalTheory.SmGL.twist_apply,
    piTensor_twist_tprod, piTensor_twist_tprod, smul_smul, ← Units.val_mul, key]

theorem levi_equiv (ρ : Representation ℂ (GL (Fin a) k) V) (s t : Fin d → ℂ)
    (hst : ∀ i, t i = ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + s i)
    (ψ : Fin d → GL (Fin a) k →* ℂˣ) (hψ : ∀ i, ψ i = detChar (Fin a) (absPow k (t i))) :
    Nonempty ((piTensor fun i => GlobalTheory.SmGL.twist ρ (detChar (Fin a) (absPow k (s i)))).Equiv
      (GlobalTheory.SmGL.twist (piTensor fun i => GlobalTheory.SmGL.twist ρ (ψ i)) (deltaHalf k fun _ : Fin d => Fin a)⁻¹)) := by
  obtain rfl : ψ = fun i => detChar (Fin a) (absPow k (t i)) := funext hψ
  exact ⟨.mk (.refl ℂ _) fun g => by
    rw [levi_eq ρ s t hst]
    rfl⟩

end Local

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem loc_eq_absPow {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (w : HeightOneSpectrum (𝓞 E)) :
    ν.loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) s := by
  ext x
  have hgeneral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (x : kˣ) :
      GlobalTheory.SplitWeil.nabs k x = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-GlobalTheory.SmGL.ord k x) := by
    open ValuativeRel in
    have hpow (x : kˣ) (m : ℕ) : GlobalTheory.SmGL.ord k (x ^ m) = m * GlobalTheory.SmGL.ord k x := by
      induction m with
      | zero =>
        simp only [pow_zero, Nat.cast_zero, zero_mul]
        exact GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
      | succ m ih =>
        rw [pow_succ, GlobalTheory.SmGL.ord_mul, ih]
        push_cast
        ring
    have hexists : ∃ ϖ : kˣ, GlobalTheory.SmGL.ord k ϖ = 1 ∧
        GlobalTheory.SplitWeil.nabs k ϖ = (GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
      obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
      have hp0 : (p : k) ≠ 0 := by
        intro h
        exact hp.ne_zero (Subtype.ext h)
      obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, map_zero] at hy
        exact (uniformizer_pos (R := k)).ne hy
      have hyint : y ∈ (valuation k).integer := by
        rw [Valuation.mem_integer_iff, hy]
        exact uniformizer_lt_one.le
      obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
      have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
        intro h
        exact u.ne_zero (Subtype.ext h)
      refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
      have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
        _root_.GlobalTheory.SmGL.ord_eq_one hy
      have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
        apply _root_.GlobalTheory.SmGL.ord_eq_zero
        exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
      have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
        ext
        have := congrArg Subtype.val hu
        simpa using this
      rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, hpow,
        zero_add] at hyo
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · omega
    obtain ⟨ϖ, hord, habs⟩ := hexists
    have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
      have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
      positivity
    have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
      have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
      exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
    have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
      have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, hord,
        _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
      omega
    have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
        (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
      intro m
      refine Int.induction_on m ?_ ?_ ?_
      · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
        rw [zpow_zero]
        exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
      · intro i ih
        rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, habs, hord]
        refine ⟨?_, rfl⟩
        rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
      · intro i ih
        rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, hinv, oinv]
        refine ⟨?_, by ring⟩
        rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
    set o := _root_.GlobalTheory.SmGL.ord k x
    have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
      rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
      ring
    have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
      _root_.GlobalTheory.SmGL.nabs_eq_one k
        (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
    have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
      rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
    calc _root_.GlobalTheory.SplitWeil.nabs k x
        = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
      _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
        rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]
  rw [CG.loc_eq_zpow (hν.1 w), Units.val_zpow_eq_zpow_val, hν.2.1 w, GlobalTheory.SmGL.val_absPow, hgeneral,
    GlobalTheory.LocLanglands.resCard_eq_normV, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have e : Formalism.UG.ordV E w x = -WithZero.log (Valued.v (x : w.adicCompletion E)) := by
    rw [Formalism.UG.ordV, dite_eq_right h0]
    conv_rhs => rw [← WithZero.coe_unzero h0]
    rfl
  rw [e, ← Complex.ofReal_cpow (by positivity), ← Real.rpow_intCast, ← Real.rpow_mul (by positivity),
    ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_zpow,
    ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 2
  · simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · push_cast
    ring

end PositivityTheory.RSHS.LocalComponentTwist

end
