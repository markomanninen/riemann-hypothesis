module

public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
public import Formalism.GaussJetBounds.StatementN
public import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
public import Formalism.GaussJetBounds.GenLogInverse
public import Formalism.GaussJetBounds.MonoShapeTop
public import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
public import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
public import Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
public import Formalism.GaussJetBounds.StatementQ
public import Formalism.GaussJetBounds.StatementP
public import Formalism.GaussJetBounds.GaussJetProofs.GField
public import Formalism.GaussJetBounds.GaussJetProofs.FJEval
public import Formalism.GaussJetBounds.GaussJetProofs.Labels

@[expose] public section

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)

end Formalism.DworkPowerSeriesWeights
