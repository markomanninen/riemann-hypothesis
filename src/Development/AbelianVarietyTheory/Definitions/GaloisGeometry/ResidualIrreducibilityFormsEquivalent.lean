module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
public import Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps

@[expose] public section

noncomputable section

namespace GlobalTheory.NFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem residualIrreducibility_forms_equivalent (D : D7) : SumRepresentations.adm6 D ↔ ResidualIrreducibleRankR D := Iff.rfl

end GlobalTheory.NFacts

end
