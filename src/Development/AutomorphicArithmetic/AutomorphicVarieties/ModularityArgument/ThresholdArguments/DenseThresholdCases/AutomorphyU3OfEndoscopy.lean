module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAutI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutCsdIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWitApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactAlt

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V hiding autCsd_iso
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
theorem UpperTheory.GalN.V.modOfEnd'_alt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω}
    {B : ValuationSubring Ω} {ι : Qbar l ≃+* ℂ} (h : _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι)
    (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A))
    (h1 : OrdPt l D.η D.Ψ D.cc g₁ B r) (h2 : TypeII D.η (UnitaryThreeInertia.push A.val r)) (h3 : ∀ g ∈ D.η.ker, (r g).mat 1 1 = 1)
    (W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (h4 : ∀ g ∈ D.η.ker, (W' g).val = corner (UnitaryThreeInertia.push A.val r g).mat)
    (h5 : (W' D.cc).val.trace = 0) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (hi : Af.RepIso W' W) : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := h A r h1 h2 h3 W' h4 h5
  refine ⟨⟨f, ?_⟩, hw.weak_admissible_iso hi⟩
  obtain ⟨g, hg⟩ := hi
  let χ := cycBar ℚ Ω l ^ (-(e : ℤ))
  have htw : ∀ s, Af.tw W χ s = g * Af.tw W' χ s * g⁻¹ := by
    intro s
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  change f.Att ι (Af.tw W χ)
  refine ⟨?_, hf.2.mono fun w hw A' hA' => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · let E : (Fin 2 → Qbar l) ≃ₗ[Qbar l] (Fin 2 → Qbar l) :=
      Matrix.toLin'OfInv (Units.mul_inv g) (Units.inv_mul g)
    have hE (v : Fin 2 → Qbar l) : E v = (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).mulVec v := rfl
    have hintertwine (s : G ℚ Ω) (v : Fin 2 → Qbar l) :
        E ((Af.tw W χ s).val.mulVec v) = (Af.tw W' χ s).val.mulVec (E v) := by
      rw [hE, hE, htw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
      congr 2
      group
    intro V hV
    obtain ⟨V', hV', hcompl⟩ := hf.1 (V.map E.toLinearMap) (by
      rintro s _ ⟨v, hv, rfl⟩
      exact ⟨_, hV s v hv, hintertwine s v⟩)
    refine ⟨V'.comap E.toLinearMap, fun s v hv => ?_, ?_⟩
    · show E _ ∈ V'
      rw [hintertwine]
      exact hV' s _ hv
    · have hcompl' : IsCompl ((V.map E.toLinearMap).comap E.toLinearMap) (V'.comap E.toLinearMap) :=
        (Submodule.orderIsoMapComap E).symm.isCompl hcompl
      rwa [Submodule.comap_map_eq_of_injective E.injective] at hcompl'
  · rw [htw, (hw A' hA').1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A' hA').2 σ hσ, htw, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj]
theorem UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Pr.GdEndAlt → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt := by
  intro hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι
  obtain ⟨B, hB, -, -, -, hmem, -⟩ := dat_loc D
  obtain ⟨g₁, hM, hfin, h3, h2⟩ := H Ω K l c N e ψ D ι B hB
  have hA : FinA D g₁ := finA_of_end hL D g₁ hM B hmem hfin
  refine ⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    have hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹ := fun s hs => by
      have hright : (r s).right = 1 := (hr s).trans hs
      have hconj : conjBy (tor _ t) r s = GG.ofGL (tor _ t) * r s * GG.ofGL (tor _ t)⁻¹ := by
        rw [map_inv]
        rfl
      rw [ht, hconj, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
        SemidirectProduct.right_inl, hright, mul_one, sgnAct_one]
    have hI' : TypeI D.η (UnitaryThreeInertia.push A.val r') :=
      _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj (tor _ t) (fun s hs => by
        rw [mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]
        congr 1
        group) hI
    have hm : HasMult D.η (UnitaryThreeInertia.push A.val r') := ho.red.mult
    have hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm) :=
      ⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩
    have key := h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl
    refine _root_.UpperTheory.GalN.V.autCsd_iso_alt ?_ key
    obtain ⟨g, hg⟩ := hiso.symm'
    refine ⟨g, fun s => Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    let d : Fin 2 → (PadicAlgCl l)ˣ := ![t, t⁻¹]
    let T : GL (Fin 2) (PadicAlgCl l) :=
      Units.map (Matrix.diagonalRingHom (n := Fin 2) (α := PadicAlgCl l)).toMonoidHom
        (MulEquiv.piUnits.symm d)
    have hcorner (g : G ℚ Ω) :
        corner (conjBy (tor _ t) r g).mat = T.val * corner (r g).mat * (↑T⁻¹ : Matrix _ _ _) := by
      ext a b
      show _ = (Matrix.diagonal (fun i => (d i : PadicAlgCl l)) * corner (r g).mat *
        Matrix.diagonal (fun i => (↑(d i)⁻¹ : PadicAlgCl l))) a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
        (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
      congr 1
      · congr 1
        fin_cases a <;> simp [d, wt1]
      · fin_cases b <;> simp [d, wt1]
    let W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l) := (MulAut.conj T).toMonoidHom.comp W
    have hW' : ∀ s, W' s = T * W s * T⁻¹ := fun s => rfl
    have hII' : TypeII D.η (UnitaryThreeInertia.push A.val r') := by
      rw [ht]
      refine ⟨fun g hg a b hab => ?_, _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj T (fun s _ => ?_) hII.2⟩
      · rw [(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]
      · rw [hcorner]
        simp only [← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact _root_.UpperTheory.GalN.V.modOfEnd'_alt D h2 A r' ho hII' (fun g hg => by
      apply Subtype.ext
      show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1
      rw [ht, (conjBy_tor r t).1, h11 g hg]
      simp [wt]) W' (fun g hg => by
      rw [ht, hcorner, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by
      rw [hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2]) W (Af.RepIso.symm' ⟨T, hW'⟩)
end
