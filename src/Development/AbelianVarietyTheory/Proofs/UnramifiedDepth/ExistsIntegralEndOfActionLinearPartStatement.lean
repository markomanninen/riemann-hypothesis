module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart
public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
public import Formalism.LocalToGlobal.CharacterGerms.NegMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEnd_of_action_linearPart : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  first | exact @GlobalTheory.ActionEnd.exists_isEnd_act | exact GlobalTheory.ActionEnd.exists_isEnd_act | (intros; apply GlobalTheory.ActionEnd.exists_isEnd_act <;> assumption)
