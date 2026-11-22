module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
public import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeGapDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound

@[expose] public section

open MeasureTheory Matrix Filter Topology Finset
open scoped InnerProductSpace ContDiff Convolution

noncomputable section

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

def thrE {n : ℕ} (ε : Fin n → Bool) : ℝ :=
  max (thrDS ε) (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℕ) + 8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)))

theorem thrE_le {n : ℕ} (ε : Fin n → Bool) (hn : (5 : ℝ) ≤ n) : thrE ε ≤ 4 * (n : ℝ) ^ 3 := by
  have hpn : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hm : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ≤ n := by exact_mod_cast (min_le_left _ _).trans hpn
  have hm0 : (0 : ℝ) ≤ ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := thrDS_le ε
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  unfold thrE
  generalize ((min (pOf ε) (qOf ε) : ℕ) : ℝ) = q at hm hm0 ⊢
  have hs0 : 0 ≤ Real.sqrt (2 * q) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by linarith)
  have hsn : Real.sqrt (2 * q) ≤ n := by nlinarith
  apply max_le
  · linarith
  · have hnq : (n : ℝ) * q ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hm (by linarith)
    nlinarith

end Formalism.MainNotions.GapDS

namespace Formalism.MainNotions.BridgeCPX

open Formalism.MainNotions.S Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HCMultDSG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    Formalism.MainNotions.GapDS.thrDS ε < h → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

section Final

open Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData Formalism.BasicNotions

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Final

end Formalism.MainNotions.BridgeCPX

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def DiscreteSeriesExistsG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε < h →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

def LowKMultOneG : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'

end Formalism.MainNotions.DiscreteSeriesWeylDimension

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S

def deg_DSUniqG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsHCParam lam → IsDS ε lam σ → IsDS ε lam σ' → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.LeviCoordinates

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

end Formalism.MainNotions.LeviCoordinates

namespace Formalism.MainNotions.TheoremBConstants

open Formalism.QuantumDeterminants Formalism.MainNotions.S

end Formalism.MainNotions.TheoremBConstants

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

end Formalism.MainNotions.LowestKTypeMultiplicity

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants
open Formalism.QuantumDeterminants.WeylGroupFacts

end Formalism.MainNotions.DiscreteSeriesInnerProducts

end

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

noncomputable def thrX {n : ℕ} (ε : Fin n → Bool) : ℝ :=
  max (thrDS ε) (120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))

theorem thrX_le {n : ℕ} (ε : Fin n → Bool) (hn : (900 : ℝ) ≤ n) : thrX ε ≤ 4 * (n : ℝ) ^ 3 := by
  have hpn : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hmn : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ≤ n := by exact_mod_cast (min_le_left _ _).trans hpn
  have hm0 : (0 : ℝ) ≤ ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hm0 hmn (by norm_num)
  have hsplit : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have h30 : (30 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith
  have h1 := thrDS_le ε
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  unfold thrX
  apply max_le
  · linarith
  · rw [hsplit] at hpow
    have hB : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * n * (n * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hC : 120 * (n : ℝ) * (n * Real.sqrt n) ≤ 4 * (n : ℝ) ^ 3 := by
      generalize Real.sqrt (n : ℝ) = s at hs0 hs2 h30 ⊢
      rw [← hs2]
      nlinarith [mul_nonneg (pow_nonneg hs0 5) (sub_nonneg.2 h30)]
    linarith

end Formalism.MainNotions.GapDS

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

end Formalism.MainNotions.DiscreteSeriesWeylDimension

namespace Formalism.MainNotions.TheoremBConstants

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

end Formalism.MainNotions.TheoremBConstants

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants
open Formalism.QuantumDeterminants.WeylGroupFacts

end Formalism.MainNotions.DiscreteSeriesInnerProducts

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

end Formalism.MainNotions.GapDS
