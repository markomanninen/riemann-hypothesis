module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

@[expose] public section

noncomputable section

open Module NumberField
open scoped InnerProductSpace

namespace GlobalTheory.LiftTestCompare

section Lin

open Matrix

variable {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

end Lin

section Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem liftTest_of_liftTestB {b : Bool} (h : LiftTestB X b) : LiftTest X := fun j => by
  obtain ⟨N, ψ, h1, h2, -⟩ := h j
  exact ⟨N, ψ, h1, h2⟩

end Cx

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Real

section ArchimedeanLeafBounds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem toCx3_liftTestB (b : Bool) :
    LiftTestB (R.toCx3 F) b ↔ LiftTestB (cxPhase R.toRealDat F.lv2 fun j => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j)) b := by
  rw [cxPhase_eq]
  simp only [cj_cj]
  exact Iff.rfl

end ArchimedeanLeafBounds

end GlobalTheory.LiftTestCompare
