module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseTAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open NumberField Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep

noncomputable section

namespace GuIrrCaseTDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

omit [NumberField L] [IsCMField L] in
private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinearMap P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end GuIrrCaseTDualProof

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]
private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]
theorem UpperTheory.V.Z.Win.Gu.irrCaseT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → IrrCaseT := by
  intro PH E Ω _ _ _ _ _ _ l _ ι n hn1 π hπ c a d hn P ρ m σ H hsp hsplit hun hc hd r hr hF
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  obtain rfl : a = fun _ => n := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hn
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, GuIrrCaseTDualProof.dualIsConj_of_isCsd (PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) (H.csd 0),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_one w S ▸ h2⟩⟩, hw, fun w h => hun w h 0, fun w hs τ hτ => ?_⟩
  · obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E _ hn1 π hπ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · obtain ⟨e₁⟩ := PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange.oneFactor E w n hn (ρ 0 w) (σ · w) (hsp 0 w)
    obtain ⟨e₂⟩ := LocUniq.isLocComp_unique (P 0) w _ _ (H.loc 0 w) hτ
    exact GlobalTheory.BaseChangeBridge.isCompAlong_of_equiv (e₁.trans e₂).toLinearEquiv
      (fun g x => LinearMap.congr_fun ((e₁.trans e₂).toIntertwiningMap.isIntertwining' g) x) τ.irred (hsplit w hs)
end
