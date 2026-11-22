module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisBis
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
public import GroundTheory.HeightsAndTheta.Heights.Intersections.SpanSingletonEqRangeLsmul
public import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLength
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalFinite.proof (hD : regularityLocalDimension_holds.Statement) : RegularityLocalFinite.Statement := by
  intro K _ ι _ P s a W y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  have hfinRes : Finite (IsLocalRing.ResidueField (locRing P W)) :=
    (regularityLocalResidue_holds.proof K ι P s a W (fun i => i.elim0) hP hs hsP hW).1
  letI := hfinRes
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  have hcard := card_eq_card_residueField_pow_length (locRing P W ⧸ locIdeal P W y) hfin
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField (locRing P W)) := Nat.card_pos
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hpos.ne'

end

end GroundTheory.Heights₂.Heights.Inter
