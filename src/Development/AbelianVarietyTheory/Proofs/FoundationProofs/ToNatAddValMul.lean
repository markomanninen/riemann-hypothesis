module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.NormValExt

open IsDiscreteValuationRing

variable {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem toNat_addVal_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (addVal R (a * b)).toNat = (addVal R a).toNat + (addVal R b).toNat := by
  rw [addVal_mul]
  exact ENat.toNat_add (fun h => ha ((addVal_eq_top_iff).mp h)) (fun h => hb ((addVal_eq_top_iff).mp h))

theorem nval_mul (l : ℕ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    BlochKatoReduction.Gen.nval R l (a * b) =
      BlochKatoReduction.Gen.nval R l a + BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.nval
  rw [toNat_addVal_mul ha hb, Nat.cast_add, add_div]

theorem vK_eq (l : ℕ) {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) :
    BlochKatoReduction.Gen.vK R l x =
      BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.vK
  generalize_proofs hE
  have hinj := IsFractionRing.injective R (FractionRing R)
  have key : ∀ q : R × nonZeroDivisors R,
      x * algebraMap R (FractionRing R) q.2 = algebraMap R (FractionRing R) q.1 →
      BlochKatoReduction.Gen.nval R l q.1 - BlochKatoReduction.Gen.nval R l q.2 =
        BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
    intro q hq
    have hq2 : (q.2 : R) ≠ 0 := nonZeroDivisors.ne_zero q.2.2
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hb) h
    have hq1 : q.1 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hq
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hq2) hq
    have hcross : a * q.2 = q.1 * b := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hq]
      ring
    have hc := congrArg (BlochKatoReduction.Gen.nval R l) hcross
    rw [nval_mul l ha hq2, nval_mul l hq1 hb] at hc
    linarith
  exact key hE.choose hE.choose_spec

end GlobalTheory.NormValExt
