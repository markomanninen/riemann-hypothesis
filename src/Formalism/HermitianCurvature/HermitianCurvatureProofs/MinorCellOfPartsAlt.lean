module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

theorem minor_cell_of_parts : PBN.MinorCellOfParts := by
  intro hRR hLR hTC hGP k r Wp Wq _ _ _ _ _ _ Bs F y hF x hx
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨hf, hLf, hRf, -⟩ := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq Bs F ε hε hn
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D (B.JF Bs F), cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl

  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    have hloc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)),
        (∀ c ∈ OmX r, f₁ c = f₂ c) → ∀ c ∈ OmX r,
        (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
        (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
      intro i
      induction i with
      | zero => intro f₁ f₂ h c hc; exact ⟨h c hc, rfl⟩
      | succ i ih =>
        intro f₁ f₂ h c hc
        have hih := ih f₁ f₂ h
        by_cases hi : i < r
        · simp only [Q.vAB, dif_pos hi]
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
            have hev : (Q.vAB r y i).1 f₁ =ᶠ[nhds c] (Q.vAB r y i).1 f₂ := by
              filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using (hih c' hc').1
            simp only [pOp, wirt, if_pos hc, hev.fderiv_eq, (hih c hc).1, (hih c hc).2]
          · simp only [ciOp, (hih c hc).1]
        · simp only [Q.vAB, dif_neg hi]
          exact hih c hc
    refine (hloc r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1

  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (E := Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D (B.JF Bs F)) (B.JF Bs F) (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

end Formalism.FourierDecayAlt.P
