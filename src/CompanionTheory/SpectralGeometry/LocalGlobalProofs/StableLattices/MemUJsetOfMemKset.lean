module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KsetSubset

@[expose] public section

open Matrix
open PI.UpqRep (UJset Kset IsKFin IsKStableOn)

namespace GlobalTheory.CompanionTheory.KFinStab

theorem kFinStab : CompanionTheory.D.DSIC.KFinStab :=
  _root_.UpperTheory.Reformulated.B.Gc1.kFinStab

end GlobalTheory.CompanionTheory.KFinStab
