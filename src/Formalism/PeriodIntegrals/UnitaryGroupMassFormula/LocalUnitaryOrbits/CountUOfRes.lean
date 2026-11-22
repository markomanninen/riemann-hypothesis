module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRedU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt

@[expose] public section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol Formalism.L2.SG.Sub NumberField IsDedekindDomain

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem redU_of_norm (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : RedU σ J ψ v Λ a Y :=
  redU_of σ J ψ v Λ (Orb.unitV_of σ J ψ v Λ hN hUN) hR a Y

theorem countU_of_res (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : CountU σ J ψ v Λ a Y :=
  countU_of_bas' σ J ψ v Λ a Y (by
    classical
    intro hG
    obtain ⟨L, hLat, hL⟩ := hG.2.1
    subst Λ
    let M := latLoc (E := E) v (L : Set (Fin n → E))
    have hfg : M.FG := basLat_fg v L hLat
    have hspan : Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
      have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
      have hopen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hG.2.2.1 hfg
      rw [eq_top_iff]
      intro x _
      obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v
        (hopen.mem_nhds M.zero_mem) (fun _ : Unit => x)
      have hmem : t • x ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
        Submodule.subset_span (htx ())
      have hx : t⁻¹ • (t • x) ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
        Submodule.smul_mem _ t⁻¹ hmem
      rwa [inv_smul_smul₀ ht] at hx
    have : Submodule.IsFullLattice (Fv F v) M :=
      { toIsLattice := Submodule.IsLattice.of_fg (Fv F v) hfg, span_eq_top := hspan }
    have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 hfg
    have : Module.Free (v.adicCompletionIntegers F) M := Submodule.IsLattice.free (Fv F v) M
    let b := Module.finBasis (v.adicCompletionIntegers F) M
    let B := b.extendOfIsFullLattice (Fv F v)
    have hB (i) : B i = (b i : Fin n → Fv F v ⊗[F] E) :=
      Module.Basis.extendOfIsFullLattice_apply (Fv F v) b i
    have hmem (x : Fin n → Fv F v ⊗[F] E) : x ∈ M ↔
        ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
          x = ∑ i, (c i : Fv F v) • B i := by
      constructor
      · intro hx
        refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
        have h := congrArg (fun y : M => (y : Fin n → Fv F v ⊗[F] E)) (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm.trans (Finset.sum_congr rfl fun i _ => by rw [hB]; rfl)
      · rintro ⟨c, rfl⟩
        exact Submodule.sum_mem M fun i _ => by rw [hB]; exact M.smul_mem (c i) (b i).2
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h2 : Module.finrank F E = 2 := hG.1.1.2.2.1
    have hm : Module.finrank (v.adicCompletionIntegers F) M = 2 * n := by
      have h := Module.finrank_eq_card_basis B
      rw [Fintype.card_fin] at h
      rw [← h, Module.finrank_pi_fintype]
      simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [← hm]
    exact ⟨B, B.linearIndependent, hmem⟩) (resIdx_holds v)
    (redU_of_norm σ J ψ v Λ hN hUN hR a Y)

end PI.OmLocU.Red
