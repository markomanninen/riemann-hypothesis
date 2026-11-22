module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

section Places

variable (F : Type) [Field F] [NumberField F]

abbrev Pl : Type := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

variable {F}


end Places

section Quat

variable {F : Type} [Field F]

variable {d β : F} {R : Type} [CommRing R] [Algebra F R]

section Top

variable [TopologicalSpace R]

end Top

end Quat

section QuatAlg

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

end QuatAlg

section Adelic

variable {F : Type} [Field F] [NumberField F] {d β : F}

end Adelic

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Two

end GlobalTheory.CompanionTheory.PlaneSA
