module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumNat_of :
    SumNat := by
  intro R _ F Z S p w A B t a b hB Ω _ _ x
  rw [res_res, hB Ω (x ≫ t.g)]
  symm
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ t.k) (fib_bijOn t.isPullback x) ?_
  intro z _
  simp only [res_res, Category.assoc, t.hv]
