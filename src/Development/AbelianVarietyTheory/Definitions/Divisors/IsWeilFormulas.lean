module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]


variable (F κ) in
def IsTamagawa [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F)) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕 : Set (κ → AF F), μ 𝓕 = 1 ∧
    IsAddFundamentalDomain (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range 𝓕 μ

end GlobalTheory.SWLit

end
