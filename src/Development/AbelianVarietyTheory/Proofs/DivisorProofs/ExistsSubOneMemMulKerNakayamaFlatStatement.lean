module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlat
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_one_mem_mul_ker_nakayama_flat : ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C'] [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f → ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f → RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) → ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  first | exact @GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le | exact GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le | (intros; apply GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le <;> assumption)
