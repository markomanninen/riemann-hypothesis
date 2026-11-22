module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryComponentUniquePrimeDimThirteenNearBase

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

theorem UpperTheory.V.Loc.rtBasic :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)), D.primesAt0 U = {D.It U} ∧ (D.It U).IsPrime ∧ (l : U.R) ∉ D.It U ∧ D.Icr U ≤ D.It U ∧ ringKrullDim (D.Rt U) = 13 ∧ D.On U (r0 D.η D.Ψ) ∧ ∀ x, IsBase D.η D.Ψ U.r.hom x → ∃ y, x y ≠ 0 ∧ ∀ a ∈ D.It U, y * a ∈ D.Icr U :=
  fun hP => @GlobalTheory.OrdLoc.component_basic hP
