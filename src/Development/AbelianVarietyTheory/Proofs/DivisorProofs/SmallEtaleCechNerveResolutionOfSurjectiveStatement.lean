module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (exact GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (intros; apply GlobalTheory.EtC.SmallEtaleCech.hyp_coAug <;> assumption)
