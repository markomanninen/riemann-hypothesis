module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatrices
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellVolumeMulCoef

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellIdx

section Abstract

variable {G : Type} [Group G] (M N K : Subgroup G)

variable {M N K}

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Abstract

end GlobalTheory.CellIdx

namespace GlobalTheory.CellIdx
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.LocGrpIff GlobalTheory.RowRep

section Flag
variable {D : D7} {K : Type} [Field K] (π : AE D →+* K) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

variable {Y₀ : Type} [Fintype Y₀] [DecidableEq Y₀] (b : Matrix (Fin S₀.rank) Y₀ K) (b' : Matrix Y₀ (Fin S₀.rank) K)

end Flag

variable {D : D7}

end GlobalTheory.CellIdx

namespace GlobalTheory.CellIdx
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.RowRep GlobalTheory.SplitWeil

section Local
variable {k : Type} [Field k]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


set_option maxHeartbeats 1600000 in
theorem vol_mul_colCoef : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D,
    ∀ la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), la.IsHaarMeasure →
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ t β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      la.real {n | (⟨b j, hb⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hb⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} *
        (GlobalTheory.RowWt.colCoef ch t β j : ℝ) = V₀ := by
  first
  | (exact @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef)
  | exact @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef
  | exact _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef
  | (apply _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef ..)

end GlobalTheory.CellIdx

end
