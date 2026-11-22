module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacTwistMapSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTransposeInvTranspose

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.srcGood :
    UpperTheory.Gal.TP.Loc.SrcGood := by
  intro k _ _ _ _ n c V _ _ σ hc hu hs hirr hun
  have hcont : Continuous (GlobalTheory.SplitFlip.invT : GL (Fin n) k →* GL (Fin n) k) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun h : GL (Fin n) k => ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_coe_inv.matrix_transpose
    · show Continuous fun h : GL (Fin n) k => (h : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_val.matrix_transpose
  refine ⟨?_, ?_, ?_⟩
  · exact isSmooth_twist (isSmooth_comp hs _ hcont) hc.detChar
  · have ht {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
        {ρ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (χ : G →* ℂˣ) :
        (twist ρ χ).IsIrreducible := by
      let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have h := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          simpa [twist_apply, smul_smul] using h⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
      exact e.isSimpleOrder_iff.2 hρ
    exact ht (GlobalTheory.InvTransposeEnds.isIrreducible_comp hirr _
      fun h => ⟨GlobalTheory.SplitFlip.invT h, GlobalTheory.SplitFlip.invT_invT h⟩) _
  · obtain ⟨B, h1, h2, h3⟩ := hun
    refine ⟨B, h1, h2, fun g v w => ?_⟩
    rw [src_apply, src_apply, LinearMap.map_smul B, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have hn := hu (Matrix.GeneralLinearGroup.det g)
    rw [show ((c (Matrix.GeneralLinearGroup.det g) : ℂ) * (starRingEnd ℂ) (c (Matrix.GeneralLinearGroup.det g) : ℂ)) = 1 by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num, one_mul]
