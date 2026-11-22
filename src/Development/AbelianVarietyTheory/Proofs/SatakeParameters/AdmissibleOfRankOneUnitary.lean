module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitaryStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem admissible_of_rank_one_unitary : ∀ (D : D7) (T : WDTie D.nd D.naut), RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → Formalism.MainNotions.SumRepresentations.adm7 D := by
  intro D T hT h2
  exact (GlobalTheory.T.tempered_of_rank_one_unitary D T hT h2).1

end GlobalTheory.RowTie
