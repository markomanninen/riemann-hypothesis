module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.TwistAway in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (h := h) hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
