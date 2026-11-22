module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockHerm
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockPos
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem bidetMem : BideterminantMem := bideterminantMem
theorem hwMem : HWMem := highestWeightVectorMem
theorem hwNe : HWNe := highestWeightVectorNeZero
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
theorem weylLeDual : WeylLeDual := by
  intro R _ r n hn ν hν
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hwMem R r n hn ν hν
  | cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
theorem bidetDominance : BideterminantDominance := bideterminantDominance
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
theorem hwRaise : HWRaise := highestWeightVectorRaising
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
theorem rowNuSum : RowNuSum := rowPartSum
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
theorem fockPos : FockPos := fischerInnerPos
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
theorem domPow : DomPow := dominancePowerProduct_holds
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end Formalism.GradedWeylDivisibility
