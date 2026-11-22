module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem card_torsion_zeros_twist_le :
    Out.Laws → Out.Laws2 → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (c : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → 1 ≤ d → (k : K) ≠ 0 → ∀ s : LB.Sec (Out.twistLB P.A P.L (N * d) c), (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) :=
  fun h _ => torsion_zero_count_twist h.mulN h.square
    (card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound)

end GlobalTheory
