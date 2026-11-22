module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

theorem isOrthCo_toLE_of_cT_mul_self {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (h : cT σ co.1 * co.1 = J) :
    IsOrthCo σ J (toLE co) := by
  intro x y
  subst h
  have ht (v : Fin N → E) : toLE co v = (co : Matrix (Fin N) (Fin N) E) *ᵥ v := rfl
  rw [ht, ht]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.TwV
