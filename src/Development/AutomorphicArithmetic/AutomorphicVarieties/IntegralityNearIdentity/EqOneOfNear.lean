module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

@[expose] public section

namespace UpperTheory.V.Lib.Small

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

end UpperTheory.V.Lib.Small
