module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem chord_of : ExpTw → SqIntCrit → Chord := by
  intro hTw hSq E _ _ _ r s hr hs V c T lam hlam hT hp hb φ hφ k g
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hdR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hd
  unfold pE at hp
  push_cast at hp
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.left φ hφ k g m₂
    refine ⟨mulChi r (Model.absC E (-(c / (r * (Module.finrank ℚ E : ℂ))))) ψ₀, aut_tw haut _, ?_,
      fun m₁ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E r _ (aut_tw haut _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₁ h1 h2 c₁ hc₁
      have h3 := hexp r₁ h1 h2 _ (hTw E r ψ₀ _ haut r₁ h1 h2 c₁ hc₁)
      have h4 := hb r₁ h1 (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.left_eq _ _ _ _ _ hr.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.left_arith r s r₁ _ lam _ _ (by exact_mod_cast hr) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.right φ hφ k g m₁
    refine ⟨mulChi s (Model.absC E (-(-c / (s * (Module.finrank ℚ E : ℂ))))) ψ₀, aut_tw haut _, ?_,
      fun m₂ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E s _ (aut_tw haut _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₂ h1 h2 c₂ hc₂
      have h3 := hexp r₂ h1 h2 _ (hTw E s ψ₀ _ haut r₂ h1 h2 c₂ hc₂)
      have h4 := hb (r + r₂) (by omega) (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.right_eq _ _ _ _ _ hs.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.right_arith r s r₂ _ lam _ _ (by exact_mod_cast hs) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4

end PositivityTheory.Rg.Rs
