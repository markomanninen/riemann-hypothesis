module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFull

theorem baseFrame_one_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (h : Lev.IsBaseFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

theorem latAt_isFullLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)), Submodule.IsFullLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  intro D ρ hρ i j b h
  open Matrix in
  have heq : (ρ.B i j b).latAt (finPt (Vc D j) h) = Bridge.hLat (Vc D j) (finPt (Vc D j) h) := by
    have hΛ := baseFrame_one_eq _ _ _ (hρ.latS i j b)
    have e : Bridge.hLat (Vc D j) (finPt (Vc D j) h) = Submodule.span (𝓞 D.host.E) {x : Fin (Vc D j).rank → D.host.E |
        Matrix.mulVec ((finPt (Vc D j) h).1⁻¹).1 (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
          GlobalTheory.AdLat.hat D.host.F ((ρ.B i j b).F.ΛS : Set (Fin (Vc D j).rank → D.host.E))} := by
      unfold Bridge.hLat
      rw [hΛ]
      rfl
    rw [e, ← Submodule.span_eq ((ρ.B i j b).latAt (finPt (Vc D j) h))]
    congr 1
    ext x
    have e : ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
        fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E ((((finPt (Vc D j) h).1⁻¹).1 *ᵥ (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
      rw [← map_inv]
      funext i
      change _ = Lev.swapAE D _
      rw [RingHom.map_mulVec (Lev.swapAE D)]
      rfl
    change ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (ρ.B i j b).F.ΛS ↔ _
    rw [e]
    constructor
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat (ρ.B i j b).F.ΛS _ hz
      simpa only [Set.mem_setOf_eq, AlgEquiv.symm_apply_apply] using this
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL (ρ.B i j b).F.ΛS _ hz
  rw [heq]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
  obtain ⟨Λ, hΛ, hΛfg, hΛspan, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E
    (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) (finPt (Vc D j) h).1 hfg hspan
  rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat _ _).trans hΛ.symm)]
  exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E hΛfg, span_eq_top := hΛspan }

theorem latAt_isLattice (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)) : Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) :=
  (latAt_isFullLattice D ρ hρ i j b h).toIsLattice

end GlobalTheory.LatFull
