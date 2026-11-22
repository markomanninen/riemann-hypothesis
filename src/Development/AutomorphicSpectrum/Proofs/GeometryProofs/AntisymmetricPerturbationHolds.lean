module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymPerturbation
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymStability
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymDivisible

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem antisymPerturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement :=
  GroundTheory.Heights₂.Heights.AntisymPerturbation.proof
    (GroundTheory.Heights₂.Heights.AntisymStability.proof
      GroundTheory.Heights₂.Heights.AntisymDivisible.proof)

end GlobalTheory.CompanionTheory.Ar.Link
