module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FirstPointNeSecondPoint
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallGenHeightsNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι)
    (II : IntersectionSystem) (q : ℕ) (w : Fin q → MRing ι),
    IsIntersectionSystem II → IsSmoothHerm A → (∀ k, 0 ≤ A.a k) →
    (∀ j, IsMultiHomog (w j) fun k ↦ (A.a k).toNat) →
    (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → P ≤ Q → ∃ j, w j ∉ Q) →
    (∀ j, ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z) →
    HeightsNonneg II P A

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
