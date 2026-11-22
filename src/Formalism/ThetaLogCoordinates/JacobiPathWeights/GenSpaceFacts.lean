module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def genPoint {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n) (genMat k n)⁻¹
    (map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) G)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
