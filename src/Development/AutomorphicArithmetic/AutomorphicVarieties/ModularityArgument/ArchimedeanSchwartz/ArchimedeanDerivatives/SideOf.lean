module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K]

private theorem norm_ne (w : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  exact_mod_cast h0

private theorem euler_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerL K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerL K B S s := by
  unfold eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem eulerd_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerLd K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerLd K B S s := by
  unfold eulerLd eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

end UpperTheory.V.Z.Inf

