module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}), (∀ (x : Sec (ofRings R M) U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)), IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧ (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧ ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)), Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := GlobalTheory.etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (X := op U) m 0
      (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := GlobalTheory.etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have h := congrArg (fun f => f.hom m)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact h.symm
