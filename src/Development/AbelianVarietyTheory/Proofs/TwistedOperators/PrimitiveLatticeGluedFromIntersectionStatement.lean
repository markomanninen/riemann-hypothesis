module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  intro D u Y X ι z hl L hL hp
  obtain ⟨hlat, hglue⟩ := GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue D u Y X ι z hl L hL hp
  refine ⟨{ toIsLattice := by first | exact hlat | exact hlat.toIsLattice, span_eq_top := ?_ }, hglue⟩
  apply Submodule.eq_top_iff'.2
  intro y
  let x := (Formalism.L2.Herm.crd X).symm y
  have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
    rw [hL.2.1]
    exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.AdIsom.Unglue.exists_smul_mem L hx
  have hcy : c • y ∈ capX Y X ι L := by
    change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
    refine ⟨c • x, ?_, ?_⟩
    · change ι (c • x) ∈ L
      simpa using hcx
    · simp [x]
  have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
    Submodule.subset_span hcy
  rw [← algebraMap_smul D.host.E c] at hcy'
  have h := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
    (c : D.host.E)⁻¹ hcy'
  simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using h
