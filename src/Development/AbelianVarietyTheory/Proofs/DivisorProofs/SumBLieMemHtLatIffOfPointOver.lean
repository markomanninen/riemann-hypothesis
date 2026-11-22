module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _


variable [IsAlgClosed C] [CharZero C]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]


variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)




end GlobalTheory.CompHt.IndepPoint

namespace GlobalTheory.CompHt

open IndepPoint

end GlobalTheory.CompHt
