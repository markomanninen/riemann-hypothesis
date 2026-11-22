module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

@[expose] public section

noncomputable section

open Finset MeasureTheory
open Formalism.MainNotions.S (umat)

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

private theorem memLp_of_weighted_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (y : H)
    (hW : MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) :=
    continuous_const.inner ((hσ.2.2 y).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : Subsingleton (Formalism.REAL.UJ ε) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 (Fin.cast hn i)))⟩
    have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
    refine MemLp.of_bound hcont.aestronglyMeasurable (‖y‖ * ‖y‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖inner ℂ y (σ (umat g) y)‖ ≤ ‖y‖ * ‖σ (umat g) y‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  · refine hW.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have hs : 1 ≤ Real.sqrt (S7.hs (umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) hs

private theorem memLp_coefficients {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : G → (H →L[ℂ] H)} (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) (v w : H) :
    MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  have hall (x : H) : MemLp (fun g => inner ℂ y (ρ g x)) 2 μ :=
    GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 x
  have hinv := ((hall w).comp_measurePreserving hInv).star
  have e : star ((fun g => inner ℂ y (ρ g w)) ∘ Inv.inv) = fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs := GraphTrick.star_eq (ρ := ρ) hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e] at hinv
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hinv v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ (w : H) (σ (umat g) (v : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  let ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (umat g)
  have hone : ρ 1 = 1 := by
    change tfClRep σ (closGen E V) 1 = 1
    exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    exact hU.1.2 (umat a) (umat_mem_UJset ε a) (umat b) (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 (umat g) (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = fun g => inner ℂ (y : H) (σ (umat g) (y : H)) := by
    funext g
    change inner ℂ (y : H) (↑(tfClRep σ (closGen E V) (umat g) y0) : H) = _
    rw [tfClRep_coe σ _ (hst (umat g) (umat_mem_UJset ε g))]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    rw [hcoe]
    exact memLp_of_weighted_diagonal hσ (y : H) (hW y hyG y hyG)
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  exact memLp_coefficients (ρ := ρ) (MeasureTheory.measurePreserving_mul_right (Formalism.REAL.muG ε))
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS.G2
