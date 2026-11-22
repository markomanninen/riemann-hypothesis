module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.SuccessiveMinima.StatementMink
public import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
public import Formalism.GL3MeanSquares.ConcavityEquidistribution
public import Formalism.LogVandermondeBounds.MultinomialPowerBound

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Matrix

section CSMat

variable {ι : Type} [Fintype ι]

end CSMat

section CSSpace

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end CSSpace

section CSRecord

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end CSRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
