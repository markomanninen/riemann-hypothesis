module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SpehInfRankOneEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SpehInfLenOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakeGaloisCompatibilityOfHeckeEigensystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.HasHTOf

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Desc.P
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop : _root_.UpperTheory.V.Z.J.D.BcOfAlt := by
  intro H E Ω _ _ _ _ _ _ hE l _ hl ι n hn σ hσ R hRc hRi hR
  obtain ⟨r, HT, hc, hs, -, -, hL, -, hQ⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl ι n hn σ hσ
  have hss : Formalism.MainNotions.N.IsSSRep R := by
    intro M hM
    rcases hRi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hRi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have hunram : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU σ w := by
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
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary
      E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hAway : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.1 hw)
  have hAgree : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      IsSplitAt w → ∃ B, FrobEig ι R w B ∧ FrobEig ι r w B := by
    filter_upwards [hR, hAway, hunram] with w h1 hw hu hsp
    obtain ⟨τ, -, h2, h3⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨σ, hσ⟩ w hsp
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h3.1 hu)
    obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
    have k : _root_.UpperTheory.V.Z.Win.LocGlobT ι r w τ := (hL w hsp τ h2).1
    exact ⟨_, _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n R hRc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (h1 hsp τ h2) hw),
      _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n r hc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT k hw)⟩
  have hiso : RepIso R r := by
    have hChar : ∀ g : G E Ω, (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
      intro g
      ext i
      have hRcoeff : Continuous fun g : G E Ω =>
          (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hRc.comp continuous_inv))
      have hrcoeff : Continuous fun g : G E Ω =>
          (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hc.comp continuous_inv))
      refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob
        (Filter.eventually_cofinite.1 hAgree) hRcoeff hrcoeff ?_) g
      intro w hw hd A hA s hFrob
      have hSplit := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
      obtain ⟨B, hB, hB'⟩ := not_not.1 hw hSplit
      have h := ((hB A hA).2 s hFrob).trans ((hB' A hA).2 s hFrob).symm
      have h' := Polynomial.map_injective ι.toRingHom ι.injective h
      rw [h']
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix R r hss hs
      (fun g => by simpa using hChar g⁻¹)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hirr : IsIrr r := by
    obtain ⟨P, hP⟩ := hiso
    refine ⟨hRi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
      (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hInv : Formalism.MainNotions.N.IsInv R (M.comap T.toLinearMap) := by
      intro g v hv
      have hComm : T ((R g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
          (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) := by
        rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
        simp [Matrix.mul_assoc]
      show T _ ∈ M
      rw [hComm]
      exact hM g _ hv
    have hMap := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hRi.2.2 _ le_top hInv with h | h
    · left
      rw [hMap, h, Submodule.map_bot]
    · right
      rw [hMap, h, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, h1, h2, -, h4, h5, h6⟩ := hQ hirr
  refine ⟨π, h1, h2, ?_, h4, h5⟩
  filter_upwards [(_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).2] with w ⟨B, hB⟩ hsp
  obtain ⟨τ, hτ⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact ⟨τ, B, h6 w hsp τ hτ, ((_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).1 w τ hτ B).1 hB, hB⟩
end
