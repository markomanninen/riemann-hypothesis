module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def big (δ : E) : Spc F E 3 := ⟨!![0, 0, 1; 0, δ, 0; -1, 0, 0], ⊥, fun _ => 1, fun _ => 1⟩


variable (F) in
def small (δ : E) : Spc F E 1 := ⟨!![δ], ⊥, fun _ => 1, fun _ => 1⟩



end GlobalTheory.Published.LeviCentreModel

end
