module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviPlaneSection

open Matrix

section Alg

variable {S : Type*} [CommRing S] {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}

end Alg

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Forms


end GlobalTheory.LeviPlaneSection

end
