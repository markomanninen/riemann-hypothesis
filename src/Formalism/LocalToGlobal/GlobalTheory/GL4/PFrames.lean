module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.SuccessiveMinima.StatementMink
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem isLattice_between {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (A B : Submodule (𝓞 E) W) (hA : Submodule.IsLattice E A) (hAB : A ≤ B) (T : ℕ) (hT : T ≠ 0)
    (hTB : ∀ x ∈ B, (T : E) • x ∈ A) : Submodule.IsLattice E B := by
  let f : W →ₗ[𝓞 E] W := ((T : ℕ) : 𝓞 E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((T : ℕ) : E) • x = ((T : ℕ) : E) • y := by
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective W (by exact_mod_cast hT : ((T : ℕ) : E) ≠ 0) h1
  have hmap : B.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hTB x hx
    simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using h1
  haveI : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA.fg
  have hmfg : (B.map f).FG := by
    have h1 := IsNoetherian.noetherian ((B.map f).comap A.subtype)
    have h2 := h1.map A.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hmap] at h2
  refine ⟨Submodule.fg_of_fg_map_injective f hf hmfg, ?_⟩
  intro s hs hli
  let g : W →ₗ[E] W := ((T : E) • LinearMap.id)
  have hg : Function.Injective g := smul_right_injective W (by exact_mod_cast hT : (T : E) ≠ 0)
  have hgs : g '' s ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    have hxB : x ∈ B := hs hx
    have hmul := hTB x hxB
    simpa [g, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hmul
  have hli' : LinearIndepOn (𝓞 E) id (g '' s) := by
    apply LinearIndepOn.image (f := g.restrictScalars (𝓞 E)) hli
    simp [LinearMap.ker_eq_bot.mpr hg]
  have hli'' : LinearIndepOn E id (g '' s) := hA.linearIndepOn _ hgs hli'
  exact (linearIndepOn_id_imageₛ_iff (f := g) hg.injOn).mp hli''

end Gen

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
