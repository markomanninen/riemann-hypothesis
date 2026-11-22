module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

def ptE (t : E) (x : Fin 2 → maximalRealSubfield E) : E := ((x 0 : maximalRealSubfield E) : E) * t + ((x 1 : maximalRealSubfield E) : E)

theorem ptE_smul (t : E) (a : OF E) (x : Fin 2 → maximalRealSubfield E) :
    ptE t (a • x) = algebraMap (OF E) E a * ptE t x := by
  simp only [ptE, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  push_cast
  have h : (((algebraMap (OF E) (maximalRealSubfield E) a) : maximalRealSubfield E) : E) = algebraMap (OF E) E a := rfl
  rw [h]; ring

end GlobalTheory.RoadE
