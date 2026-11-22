module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo

@[expose] public section

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def cutL {n : ℕ} (U : Set k) : (Mx k n → ℂ) →ₗ[ℂ] (GL (Fin (n + 1)) k → ℂ) where
  toFun ψ x := by
    classical
    exact if (x.val).det ∈ U then ψ x.val else 0
  map_add' ψ₁ ψ₂ := funext fun x => by
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
open Classical in
theorem cutL_apply {n : ℕ} (U : Set k) (ψ : Mx k n → ℂ) (x : GL (Fin (n + 1)) k) :
    cutL U ψ x = if (x.val).det ∈ U then ψ x.val else 0 := by
  classical
  rfl

theorem mem_SB_iff_supportedIn {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ f ∈ supportedIn (Set.univ : Set X) := by
  constructor
  · intro h
    exact ⟨h, Set.subset_univ _⟩
  · intro h
    exact h.1

theorem cutL_mem {n : ℕ} (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) {ψ : Mx k n → ℂ}
    (hψ : ψ ∈ SB (Mx k n)) : cutL U ψ ∈ SB (GL (Fin (n + 1)) k) := open Topology Filter in by
  have hE : IsEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
    refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
    · intro A hA
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_matrix_inv
      have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hd
    · intro u
      exact (Matrix.coe_units_inv u).symm
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    Units.continuous_val.matrix_det
  constructor
  · have h1 : IsLocallyConstant (fun x : GL (Fin (n + 1)) k => ψ x.val) :=
      hψ.1.comp_continuous Units.continuous_val
    rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
    intro x
    by_cases hx : (x.val).det ∈ U
    · have h2 : ∀ᶠ x' in nhds x, (x'.val).det ∈ U :=
        hdet.continuousAt.preimage_mem_nhds (hU.isOpen.mem_nhds hx)
      filter_upwards [h2, h1 x] with x' hx' h'
      simp only [cutL_apply, if_pos hx, if_pos hx', h']
    · have h2 : ∀ᶠ x' in nhds x, (x'.val).det ∈ Uᶜ :=
        hdet.continuousAt.preimage_mem_nhds (hU.isClosed.isOpen_compl.mem_nhds hx)
      filter_upwards [h2] with x' hx'
      have hx'' : (x'.val).det ∉ U := hx'
      simp only [cutL_apply, if_neg hx, if_neg hx'']
  · have hK : IsCompact (tsupport ψ ∩ (fun A : Mx k n => A.det) ⁻¹' U) :=
      hψ.2.isCompact.inter_right (hU.isClosed.preimage continuous_id.matrix_det)
    have hKr : tsupport ψ ∩ (fun A : Mx k n => A.det) ⁻¹' U ⊆
        Set.range (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
      intro A hA
      have hd : A.det ≠ 0 := by
        intro h
        exact h0 (h ▸ hA.2)
      exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hd)).unit,
        IsUnit.unit_spec _⟩
    have hK' := hE.isInducing.isCompact_preimage' hK hKr
    refine HasCompactSupport.intro' hK' (hK.isClosed.preimage Units.continuous_val) ?_
    intro x hx
    rw [cutL_apply]
    split_ifs with h
    · exact image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨hm, h⟩)
    · rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_cj {n : ℕ} (p x : GL (Fin (n + 1)) k) :
    ((p * x * p⁻¹ : GL (Fin (n + 1)) k).val).det = (x.val).det := by
  simp only [Units.val_mul, Matrix.det_mul]
  rw [mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one, one_mul]

theorem cutL_cj {n : ℕ} (U : Set k) (p : GL (Fin (n + 1)) k) (ψ : Mx k n → ℂ) :
    cutL U (ψ ∘ cj p) = fun x => cutL U ψ (p * x * p⁻¹) := by
  funext x
  rw [cutL_apply, cutL_apply, det_cj]
  rfl

end PositivityTheory.RgUd.AB.Pf

namespace PositivityTheory.RgUd.AB.Pf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA_of_core : CoreX k → ThmT k → ThmA k := open Topology Filter in by
  intro hC hT n Λ hP p f hf
  classical
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf.1
  let φ : SB (GL (Fin (n + 1)) k) := ⟨f, hf'⟩
  have hE : IsOpenEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
    have hEmb : IsEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
      refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
      · intro A hA
        apply ContinuousAt.continuousWithinAt
        apply continuousAt_matrix_inv
        have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ hd
      · intro u
        exact (Matrix.coe_units_inv u).symm
    refine ⟨hEmb, ?_⟩
    have hr : Set.range (Units.val : GL (Fin (n + 1)) k → Mx k n) =
        {A | A.det ≠ 0} := by
      ext A
      constructor
      · rintro ⟨u, rfl⟩
        exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)).unit,
          IsUnit.unit_spec _⟩
    rw [hr]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let ext : Mx k n → ℂ := fun y => if h : IsUnit y then φ.1 h.unit else 0
  have ext_val (u : GL (Fin (n + 1)) k) : ext u.val = φ.1 u := by
    dsimp [ext]
    rw [dif_pos u.isUnit, IsUnit.unit_of_val_units]
  have ext_mem : ext ∈ SB (Mx k n) := by
    have hK : IsCompact (Units.val '' tsupport φ.1) := φ.2.2.isCompact.image hE.continuous
    have hKc : IsClosed (Units.val '' tsupport φ.1) := hK.isClosed
    have hzero : ∀ y, y ∉ Units.val '' tsupport φ.1 → ext y = 0 := by
      intro y hy
      dsimp [ext]
      split_ifs with h
      · exact image_eq_zero_of_notMem_tsupport (fun hm => hy ⟨h.unit, hm, h.unit_spec⟩)
      · rfl
    refine ⟨?_, HasCompactSupport.intro' hK hKc hzero⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    by_cases hy : IsUnit y
    · obtain ⟨u, rfl⟩ := hy
      have hφ := (IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 u
      rw [← hE.map_nhds_eq, Filter.eventually_map]
      filter_upwards [hφ] with u' hu'
      rw [ext_val, ext_val, hu']
    · have hy' : y ∉ Units.val '' tsupport φ.1 := by
        rintro ⟨u, -, rfl⟩
        exact hy u.isUnit
      filter_upwards [hKc.isOpen_compl.mem_nhds hy'] with y' hy''
      rw [hzero y' hy'', hzero y hy']
  let ψ : SB (Mx k n) := ⟨ext, ext_mem⟩
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  obtain ⟨U, hU, hCU, h0⟩ := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.exists_clopen_local
    ((fun x : GL (Fin (n + 1)) k => (x.val).det) '' tsupport f)
    (hf'.2.isCompact.image hdet)
    (by
      rintro ⟨x, -, hx⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero hx)
  have hfeq : cutL U ψ.1 = f := by
    funext x
    rw [cutL_apply]
    split_ifs with h
    · exact ext_val x
    · symm
      by_contra hne
      exact h (hCU ⟨x, subset_tsupport _ hne, rfl⟩)
  let Λ' : (Mx k n → ℂ) →ₗ[ℂ] ℂ := Λ ∘ₗ cutL U
  have hPX : PInvX Λ' := by
    intro q hq g hg
    show Λ (cutL U (g ∘ cj q)) = Λ (cutL U g)
    rw [cutL_cj]
    exact hP q hq _ ((mem_SB_iff_supportedIn _).mp (cutL_mem U hU h0 hg))
  have hGX := hC hT n Λ' hPX p ψ.1 ψ.2
  have e1 : (fun g => f (p * g * p⁻¹)) = cutL U (ψ.1 ∘ cj p) := by
    rw [cutL_cj, hfeq]
  have e2 : Λ (cutL U (ψ.1 ∘ cj p)) = Λ (cutL U ψ.1) := hGX
  rw [e1, e2, hfeq]

end PositivityTheory.RgUd.AB.Pf
