module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OnePlace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroInd

theorem redFn_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) (hy : y ∈ St β) : redFn β PP (x * y) = redFn β PP x * redFn β PP y := by
  unfold redFn ext1
  rw [dite_eq_left (mul_mem hx hy), dite_eq_left hx, dite_eq_left hy]
  rw [← map_mul]
  congr 1

theorem redFn_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) : redFn β PP x⁻¹ = (redFn β PP x)⁻¹ := by
  unfold redFn ext1
  rw [dite_eq_left (inv_mem hx), dite_eq_left hx]
  rw [← map_inv]
  congr 1

theorem reductionBlock_injective_of_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n = r) :
    Function.Injective (upperLeftBlock (κ := κ) hr) := by
  subst hn
  intro a b h
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

end GlobalTheory.LevZeroInd

