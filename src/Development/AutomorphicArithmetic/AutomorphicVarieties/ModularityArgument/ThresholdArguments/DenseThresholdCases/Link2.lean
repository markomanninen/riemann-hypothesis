module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobLG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
theorem link2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : Plc E, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2)
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ)
    (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hρc : Continuous ρ) (hρi : Af.IsIrr ρ)
    (hρF : ∀ᶠ w : Plc E in Filter.cofinite, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → ∀ B, GlobalTheory.LFun.HasSatGL w τ.ρ B →
        Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain ⟨r, HT, hc, hs, -, -, hLG, -, hcusp⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl2 ι n hn σ hσ
  have hoff : ∀ᶠ w : Plc E in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hunram : ∀ᶠ w : Plc E in Filter.cofinite, IsUnramU σ w := by
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    let L : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at *
          rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hagree : ∀ᶠ w : Plc E in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι ρ w B := by
    filter_upwards [hoff, hunram, hρF] with w hl hu hw hd
    have hsp := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
    obtain ⟨τ, hτ⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E n σ hσ w hsp).1
    obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.SphBC.isSpherical_of_isCompAlong_split hσ hsp τ.ρ hτ hu)
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨_, _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hl hB (hLG w hsp τ hτ).1, hw hsp τ hτ B hB⟩
  have hρss : IsSSRep ρ := fun M hM => by
    rcases hρi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hρi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have e : Af.RepIso r ρ := by
    have hchar := UpperTheory.V.Af.Es.charpoly_eq_prod ι (I := Unit) (a := fun _ => n)
      r (fun _ => ρ) hc (fun _ => hρc) (hagree.mono fun w h hd => by
        obtain ⟨B, h1, h2⟩ := h hd
        exact ⟨fun _ => B, by simpa using h1, fun _ => h2⟩)
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix
      r ρ hs hρss (fun g => by simpa using hchar g)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hri : Af.IsIrr r := by
    obtain ⟨P, hP⟩ := Af.RepIso.symm' e
    refine ⟨hρi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hi : IsInv ρ (M.comap T.toLinearMap) := fun g v hv => by
      have h1 := hM g _ hv
      change (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) ∈ M at h1
      change T _ ∈ M
      have e1 : P * ρ g = r g * P := by rw [hP g, inv_mul_cancel_right]
      rw [hT, Matrix.mulVec_mulVec, ← Units.val_mul, e1, Units.val_mul,
        ← Matrix.mulVec_mulVec, ← hT]
      exact h1
    have hm := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hρi.2.2 _ le_top hi with h0 | h1
    · left
      rw [hm, h0, Submodule.map_bot]
    · right
      rw [hm, h1, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, p1, p2, p3, -, p4, p5⟩ := hcusp hri
  refine ⟨π, p1, p2, ⟨hρss, p3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩, p4, fun w hw τ => ⟨p5 w hw τ, fun hτ => ?_⟩⟩
  obtain ⟨τ', hτ'⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact (GlobalTheory.BCT.isLocComp_iff_equiv hτ' τ).2 (UpperTheory.building_component_uniqueness E n σ hσ w hw _ _ _ _ hτ (p5 w hw τ' hτ'))
end UpperTheory.Gal.projectedFormsSystemPart
end
