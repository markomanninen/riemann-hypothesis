module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem finiteMeasure_muG_of_zero {ε : Fin n → Bool} (hn : n = 0) :
    IsFiniteMeasure (Formalism.REAL.muG ε) := by
  subst n
  have : Subsingleton (Formalism.REAL.UJ ε) :=
    ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
  have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
  infer_instance

private theorem memLp_of_weighted {ε : Fin n → Bool} {f : Formalism.REAL.UJ ε → ℂ}
    (hf : Continuous f) (C : ℝ) (hbound : ∀ g, ‖f g‖ ≤ C)
    (hweighted : MemLp (fun g =>
      (Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℂ) * f g)
      2 (Formalism.REAL.muG ε)) : MemLp f 2 (Formalism.REAL.muG ε) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have := finiteMeasure_muG_of_zero (ε := ε) hn
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  · refine hweighted.of_le hf.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have h1 : 1 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) h1

private theorem memLp_coefficients {G H : Type*} [Group G] [MeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μ : Measure G} {ρ : G → (H →L[ℂ] H)}
    (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) :
    ∀ v w : H, MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  intro v w
  by_cases hw : w = 0
  · simpa only [hw, inner_zero_left] using (MemLp.zero' : MemLp (fun _ : G => (0 : ℂ)) 2 μ)
  have hwy := GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 w
  have hInvCoeff : star ((fun g => inner ℂ y (ρ g w)) ∘ (Inv.inv : G → G)) =
      fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs : star (ρ g⁻¹) = ρ g⁻¹⁻¹ := GraphTrick.star_eq hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  have hyw : MemLp (fun g => inner ℂ w (ρ g y)) 2 μ :=
    hInvCoeff ▸ (hwy.comp_measurePreserving hInv).star
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hyw v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  set ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (Formalism.MainNotions.S.umat g) with hρ
  have hone : ρ 1 = 1 := by
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
    rw [e]; exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
    rw [e]; exact hU.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 _ (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy0, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy0
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  let f : Formalism.REAL.UJ ε → ℂ := fun g => inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) (y : H))
  have hcont : Continuous f :=
    continuous_const.inner ((hσ.2.2 _).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  have hbound (g : Formalism.REAL.UJ ε) : ‖f g‖ ≤ ‖(y : H)‖ * ‖(y : H)‖ := by
    change ‖inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) (y : H))‖ ≤ _
    calc
      _ ≤ ‖(y : H)‖ * ‖σ (Formalism.MainNotions.S.umat g) (y : H)‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = f := by
      funext g
      change inner ℂ y0 (tfClRep σ (closGen E V) (Formalism.MainNotions.S.umat g) y0) =
        inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) (y : H))
      rw [Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]
    rw [hcoe]
    exact memLp_of_weighted hcont _ hbound (hW y hyG y hyG)
  change ∀ v w : closGen E V, MemLp (fun g => inner ℂ w (ρ g v)) 2 (Formalism.REAL.muG ε)
  exact memLp_coefficients (ρ := ρ)
    (ReciprocityTheory.ChartRestriction.DS.measurePreserving_mul_right ε)
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS
