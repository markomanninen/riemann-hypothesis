module

public import Formalism.LocalToGlobal.CharacterGerms.NormOneIntegral
public import Formalism.LocalToGlobal.CharacterGerms.FinTwoNeOneSub
public import Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant
public import Formalism.LocalToGlobal.CharacterGerms.NormOneRowDegrees
public import Formalism.LocalToGlobal.CharacterGerms.RowTieGermI
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqEx
public import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
public import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
public import Formalism.LocalToGlobal.CharacterGerms.RowTieChar
public import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePNabMapSt
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePNvalEqSt
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanFinal
public import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTDone
public import Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
public import Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord
public import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
public import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear
public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfUnconditional

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem descent_holds : DescentSt Xo c := descent_of (nabMapSt_holds Xo c) descent_span nvalEqSt_holds

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

end Formalism.L2.FormalSeriesBounds
