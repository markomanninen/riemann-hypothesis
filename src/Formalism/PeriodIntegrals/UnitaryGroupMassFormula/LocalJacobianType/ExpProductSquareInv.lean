module

public import Mathlib
public import Formalism.PeriodIntegrals.LocJacTyp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

section Count

end Count

section Real

open Real

variable (r : ℕ)

end Real

section Final

open Real

end Final

section AbsProd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def absVHom : Fv F v →* ℝ where
  toFun := absV v
  map_one' := absV_one v
  map_mul' := absV_mul v

theorem absV_prod {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) :=
  map_prod (absVHom v) f s

end AbsProd

end PI.UnitaryGroupMassFormula.LocJacTyp
