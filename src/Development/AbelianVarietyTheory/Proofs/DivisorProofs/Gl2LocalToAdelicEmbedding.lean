module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.GLTwoHecke

section Matrices

variable {R : Type} [CommRing R]


end Matrices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def singleNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* FiniteAdeleRing (𝓞 E) E where
  toFun := singleFin w
  map_mul' := singleFin_mul w
  map_zero' := map_zero _
  map_add' := map_add _



end GlobalTheory.GLTwoHecke

end
