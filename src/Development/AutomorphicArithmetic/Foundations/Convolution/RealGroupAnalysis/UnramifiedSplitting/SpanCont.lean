module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.spanCont :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ Φ ∈ span W M π, Continuous Φ.1 ∧ ∀ γ h, Φ.1 (ratGL E 2 γ * h) = Φ.1 h := by
  intro F E _ _ _ _ _ _ _ D W M π Φ hΦ
  have hlevel : UpperTheory.ConvolutionTheory.R2.Ff.Level W M π := by
    intro f hf φ hφ Φ hΦ
    obtain ⟨κ, hκc, hκ⟩ := UpperTheory.ConvolutionTheory.R2.Ff.finTr F E D
    have hfo : IsOpen {k | TR.finRep F 2 k f = f} := (π.cusp f hf).1.level
    have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), TR.finRep F 2 (κ k) f = f := by
      have hm : {k | TR.finRep F 2 k f = f} ∈ 𝓝 (κ 1) := hfo.mem_nhds (by simp)
      exact hκc.continuousAt.eventually hm
    let S : Subgroup (GL (Fin 2) (Af E)) :=
      { carrier := {k | GlobalTheory.CuspRep.finRep E 2 k Φ = Φ}
        one_mem' := by simp
        mul_mem' := fun {k l} hk hl => by
          change GlobalTheory.CuspRep.finRep E 2 (k * l) Φ = Φ
          rw [map_mul, Module.End.mul_apply, hl, hk]
        inv_mem' := fun {k} hk => by
          change GlobalTheory.CuspRep.finRep E 2 k⁻¹ Φ = Φ
          conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E 2 k Φ = Φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl }
    refine Subgroup.isOpen_of_mem_nhds (H := S) (g := 1) ?_
    filter_upwards [UpperTheory.ConvolutionTheory.R2.Ff.lLevel F E D W φ, h1] with k hL hk
    refine Subtype.ext (funext fun g => ?_)
    change Φ.1 (g * finGL E 2 k) = Φ.1 g
    rw [hΦ, UpperTheory.ConvolutionTheory.R2.Ff.transl F E D W M, hL, hκ k]
    exact congrFun (congrArg (fun u => lift W M u φ) (congrArg Subtype.val hk)) g
  induction hΦ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    refine ⟨ContAut.continuous_of_isOpen_stab E 2 Ψ (hlevel f hf φ hφ Ψ e), fun γ h => ?_⟩
    rw [e]
    exact (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).1 γ h
  | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
  | add x y _ _ ix iy => exact ⟨ix.1.add iy.1, fun γ h => congrArg₂ (· + ·) (ix.2 γ h) (iy.2 γ h)⟩
  | smul c x _ ix => exact ⟨ix.1.const_smul c, fun γ h => congrArg (c • ·) (ix.2 γ h)⟩
