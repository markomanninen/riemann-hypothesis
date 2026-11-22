module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.QcontDual

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

theorem UpperTheory.V.Loc.rtTangent :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ γ ∈ Z1 (adRep (D.rz E)), ∀ r' : GQ l →* GG (m := 3) (R := DualNumber E), DualDef (D.rz E) γ r' → (D.On U r' ↔ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) :=
  fun hP => @GlobalTheory.OrdLoc.rtTangent hP
