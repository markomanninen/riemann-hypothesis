module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedSymBoxLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPowerStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

variable {S : Scheme.{0}}

def powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) : PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : IsCommMonObj A' := PowGrp.comm_of_isPowGrp p P.isAb.comm
  { A := A'
    isAb := (PowGrp.powers S A' P.A j p).2.2.2.1 P.isAb
    g := j * P.g
    smoothDim := (PowGrp.powers S A' P.A j p).2.2.1 P.g P.smoothDim
    L := boxLB P.L p.pr
    isLB := LB.isLB_linComb P.isLB _ _
    rigid := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).1 P.rigid
    sym := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).2 P.sym
    ample := T.relAmple_externalTensorPower_groupPower S A' P.A j p P.L P.isLB P.ample
    ktriv := T.kTriv_external_tensor_power_lineBundle S A' P.A j p P.L P.isLB P.ktriv }

def isPowPolAV_powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) :
    IsPowPolAV (powPolOf P A' p) P j where
  toIsPowGrp := p
  w := CubePf.idIsoL (boxLB P.L p.pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb P.isLB _ _)

def powPol (P : PolAV S) (j : ℕ) : PolAV S :=
  powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

def isPowPolAV_powPol (P : PolAV S) (j : ℕ) : IsPowPolAV (powPol P j) P j :=
  isPowPolAV_powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

theorem exists_powPolAV : ∀ (S : Scheme.{0}) (P : PolAV S) (j : ℕ),
    ∃ (P' : PolAV S) (_ : IsPowPolAV P' P j), P'.g = j * P.g :=
  fun _ P j => ⟨powPol P j, isPowPolAV_powPol P j, rfl⟩

end GlobalTheory
