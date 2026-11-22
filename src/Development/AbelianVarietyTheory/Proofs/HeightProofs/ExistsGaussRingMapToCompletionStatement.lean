module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G
open scoped TensorProduct

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance gaussStatementOpIsLocalRing : IsLocalRing (Op X la N) :=
  IsLocalization.AtPrime.isLocalRing (Op X la N) (gI X la N)

local instance gaussStatementOpIsDomain : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance gaussStatementKpField : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance gaussStatementKpAlgebra : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la)
    (g := (algebraMap (Op X la N) (FractionRing (Op X la N))).comp
      (algebraMap (X.Ol la) (Op X la N)))
    ((IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp
      (Op.algebraMap_injective X la N))).toAlgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussRing_map_to_completion :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ)
      (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ)
      (σ : T0.TVar D' N' ≃ Idx D j N),
      ∃ (f : T0.Op D' N' la →+* Op X la N) (φ : T0.KTf B.KO D' N' →+* Kp X la N),
        f.Flat ∧ IsLocalHom f ∧
        Ideal.map f (IsLocalRing.maximalIdeal (T0.Op D' N' la)) =
          IsLocalRing.maximalIdeal (Op X la N) ∧
        (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧
        (∀ o, φ (T0.OpToKT D' N' la o) = algebraMap (Op X la N) (FractionRing (Op X la N)) (f o)) ∧
        (∀ a : B.KO, φ (algebraMap B.KO (T0.KTf B.KO D' N') a) =
          algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧
        ∀ q, φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N') (MvPolynomial.X q)) =
          algebraMap (Op X la N) (FractionRing (Op X la N)) (Tv X la N (σ q)) :=
  GlobalTheory.GaussCompletion.exists_gaussRing_map

end
