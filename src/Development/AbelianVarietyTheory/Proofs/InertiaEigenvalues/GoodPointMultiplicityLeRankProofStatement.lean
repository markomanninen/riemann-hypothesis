module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPointMultiplicityLeRankProof
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPointMultiplicityLeRank_proof : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ → KillingConditions.LocalisationUniqueness D → MultLe L := by
  first | exact @GlobalTheory.NLink.multLe_of_rank | exact GlobalTheory.NLink.multLe_of_rank | (intros; apply GlobalTheory.NLink.multLe_of_rank <;> assumption)
