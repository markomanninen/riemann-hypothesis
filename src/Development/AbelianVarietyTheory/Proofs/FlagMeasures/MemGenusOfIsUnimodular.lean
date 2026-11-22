module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
public import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.ExGenus

open Formalism.HermitianLatticesTheory

private theorem full_of_unimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hu : IsUnimodular h L) :
    Submodule.IsFullLattice K L := by
  letI := hL
  refine { span_eq_top := ?_ }
  let W := Submodule.span K (L : Set V)
  change W = ⊤
  by_contra hw
  let b := Module.finBasis K V
  let e : V ≃ₗ⋆[K] V := (b.equivFun.trans (starLinearEquiv K)).trans b.equivFun.symm
  let g : V →ₗ[K] Module.Dual K W :=
    (LinearMap.domRestrict' W).comp (h.comp e.toLinearMap)
  have hd : Module.finrank K (Module.Dual K W) < Module.finrank K V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt hw
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hd)
  have hm (a : K) : a • e x ∈ L := by
    rw [← hu, dualBasic_mem_dual]
    intro y hy
    have hz : h (e x) y = 0 :=
      congrArg (fun f : Module.Dual K W => f ⟨y, Submodule.subset_span hy⟩)
        (LinearMap.mem_ker.mp hx)
    have hz' : h y (e x) = 0 := by
      exact hs.eq_iff.mp hz
    simp [LinearMap.map_smul, hz']
  let i : K →ₗ[𝓞 K] L :=
    ((LinearMap.toSpanSingleton K _ (e x)).restrictScalars (𝓞 K)).codRestrict L hm
  letI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.fg
  letI : Module.Finite (𝓞 K) K := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective K (fun hzero => hx0 (e.map_eq_zero_iff.mp hzero))
      (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField K
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))


theorem mem_genus_of_isUnimodular : ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.TypeAsm.Std D large₂ → ∀ (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 := by
  intro D large₂ hS _ _ Λ hΛ hU
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := (GlobalTheory.TypeAsm.hostC D large₂ hS).1

  have hloc : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E L →
      (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT L ↔
        ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt (VS D).hT P L) :=
    fun L hL => (Formalism.HermitianLatticesTheory.locDual (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT (VS D).herm
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).2
  have hΛfull := full_of_unimodular (VS D).hT (VS D).herm hΛ hU
  have hL0full := full_of_unimodular (VS D).hT (VS D).herm
    (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular
  refine ⟨hΛfull, fun P hP => ?_⟩

  exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt D.host.E (VS D).V (VS D).hT hCM (VS D).herm
    (VS D).nondeg (VS D).L0 Λ hL0full hΛfull P hP
    ((hloc _ (VS D).standardTuple_isLattice).1 (VS D).baseLattice_isUnimodular P hP) ((hloc Λ hΛ).1 hU P hP)

end GlobalTheory.RowsOrb.ExGenus
