module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoAltAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
namespace UpperTheory.GalN.V
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
theorem autCsd_iso_alt {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).isobaricDense h⟩
end
def AutomorphyOverRationalsIsobaricDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r
theorem autQIsoN : _root_.UpperTheory.GalN.V.AutomorphyOverRationalsIsobaricDense := by
  intro F Ω _ _ _ _ l _ ι n r r' e h hc K _ _ _ _ _ _ h2 hi
  let φ : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have e' : RepIso (r.comp φ) (r'.comp φ) :=
    e.imp fun _ hg s => hg _
  have hi' : IsIrr (r'.comp φ) := by
    obtain ⟨g, hg⟩ := e'
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    let T := Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) (Qbar l))
    have hcomm (s : G K Ω) : g * (r.comp φ) s = (r'.comp φ) s * g := by
      rw [hg s, inv_mul_cancel_right]
    have hcomap := hi.2.2 (W.comap T) le_top (fun s v hv => by
      change T ((↑((r.comp φ) s) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) ∈ W
      dsimp only [T]
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hcomm,
        Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hW s (T v) hv)
    have hsurj : Function.Surjective T := fun v =>
      ⟨(↑(g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v, by
        dsimp only [T]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mulVec]⟩
    have hmap := Submodule.map_comap_eq_of_surjective hsurj W
    rcases hcomap with hbot | htop
    · left
      rw [← hmap, hbot, Submodule.map_bot]
    · right
      rw [← hmap, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  obtain ⟨⟨π, h1, h3⟩, hw⟩ := h (continuous_of_iso hc e) K h2 hi'
  exact ⟨⟨π, h1, attC_iso e'.symm' h3⟩, hw.isobaricDense e'.symm'⟩
end UpperTheory.GalN.V
end
end
