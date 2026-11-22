module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessTotallyComplexGLProof
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL

@[expose] public section

theorem _root_.GlobalTheory.T.harishChandraFinitenessTotallyComplexGL_proof : GlobalTheory.HCF.CoreFiniteGL := by
  first | exact @GlobalTheory.HCFGL.coreFiniteGL | exact GlobalTheory.HCFGL.coreFiniteGL | (intros; apply GlobalTheory.HCFGL.coreFiniteGL <;> assumption) | exact @GlobalTheory.HCFGL.finiteDimensional_single | exact GlobalTheory.HCFGL.finiteDimensional_single | (intros; apply GlobalTheory.HCFGL.finiteDimensional_single <;> assumption)
