module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.InfTree
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open scoped Classical

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem mulChi_neg_cancel (w : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E (-w)) (mulChi a (Model.absC E w) ψ) = ψ := by
  have h := ChordArithmetic.mulChi_absC_cancel (E := E) a (-w) ψ
  rwa [neg_neg] at h

theorem isAutSt_tw {V : Submodule ℂ (Sm E a)} (hV : IsAutSt V) (w : ℂ) : IsAutSt (tw V w) := by
  refine ⟨ParabolicProjection.isStable_tw hV.1 w, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h := hV.2 ψ hψ
  let χ := Model.absC E w
  change IsAutForm (mulChi a χ ψ)
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
        ring
  }

theorem finGen_tw {V : Submodule ℂ (Sm E a)} (hV : FinGen V) (w : ℂ) : FinGen (tw V w) := by
  obtain ⟨S, hS, hgen⟩ := hV
  refine ⟨S.image (mulChi a (Model.absC E w)), ?_, fun W hW hSW => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS (Finset.mem_coe.2 hy))
  · have hle : V ≤ tw W (-w) := hgen _ (ParabolicProjection.isStable_tw hW (-w)) (fun y hy => by
      have hmem : mulChi a (Model.absC E w) y ∈ W :=
        hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))
      have h : (mulChi a (Model.absC E (-w))).toLinearMap (mulChi a (Model.absC E w) y) ∈ tw W (-w) :=
        Submodule.mem_map_of_mem hmem
      rw [LinearEquiv.coe_coe, mulChi_neg_cancel] at h
      exact h)
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 (hle hψ)
    have e := ChordArithmetic.mulChi_absC_cancel (E := E) a w χ
    simp only [LinearEquiv.coe_coe] at e ⊢
    rw [e]
    exact hχ

theorem infNodup_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (h : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (w : ℂ) :
    ∃ m, HasInfCharGL (tw V w) τ m ∧ m.Nodup := by
  obtain ⟨m, hm, hnd⟩ := h
  exact ⟨m.map (· + w), SpectralAccumulation.Trees.hasInfCharGL_tw hm w, hnd.map (add_left_injective w)⟩

theorem regAll_tw {V : Submodule ℂ (Sm E a)} (hV : RegAll V) (w : ℂ) : RegAll (tw V w) :=
  fun τ => infNodup_tw (hV τ) w

theorem hyp_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (w : ℂ) (hA : IsAutSt V) (hF : FinGen V)
    (hI : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (hR : RegAll V) (hN : SpectralAccumulation.NonPos (tw V w)) (hC : SpectralAccumulation.CentIm (tw V w)) :
    Hyp τ (tw V w) :=
  ⟨isAutSt_tw hA w, finGen_tw hF w, hN, hC, infNodup_tw hI w, regAll_tw hR w⟩

theorem tw_tw_neg (V : Submodule ℂ (Sm E a)) (w : ℂ) : tw (tw V (-w)) w = V := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hχ
    simp only [LinearEquiv.coe_coe]
    rw [ChordArithmetic.mulChi_absC_cancel]
    exact hψ
  · intro hφ
    have h1 : (mulChi a (Model.absC E (-w))).toLinearMap φ ∈ tw V (-w) := Submodule.mem_map_of_mem hφ
    have h2 := Submodule.mem_map_of_mem (f := (mulChi a (Model.absC E w)).toLinearMap) h1
    simp only [LinearEquiv.coe_coe] at h2
    rw [ChordArithmetic.mulChi_absC_cancel] at h2
    exact h2

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
