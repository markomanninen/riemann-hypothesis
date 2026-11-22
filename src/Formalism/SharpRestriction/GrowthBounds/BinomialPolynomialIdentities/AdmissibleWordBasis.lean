module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsDominantTopWeightNonzero
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.CardPathIndexWeightMemEqMulChoose
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.TorusComponentMemDominatedWeightPolynomials

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem restOne : RestOne := restOne_of restWord restTop restSplit

theorem admissible_word_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.FirstLettersLowerSet D := firstLettersLowerSet_of_restWord_restOne D restWord restOne

end Formalism.MainNotions.G.ColumnFamilies
