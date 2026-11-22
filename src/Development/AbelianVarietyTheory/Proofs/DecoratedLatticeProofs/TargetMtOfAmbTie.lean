module

public import Mathlib
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
public import Formalism.LocalRingCardinality.DataArith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.Statement
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.Columns.RowFormsGood
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas

@[expose] public section

open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.AmbTieStep
