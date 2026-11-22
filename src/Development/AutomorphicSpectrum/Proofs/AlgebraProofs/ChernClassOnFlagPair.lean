module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinDivDiffExpansion
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointFlagModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinPointIdeal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinDivCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinVariety
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinIntNum
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointVertDiv
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependentStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependentStatement

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial

open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial

theorem rootPolyNum : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous d := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h3
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ]
    exact Finsupp.hasFiniteSupport _
  have hcast : Fin.append x L ∘ Fin.castAdd q = x := by
    funext i
    simp [Fin.append_left]
  have hnat : Fin.append x L ∘ Fin.natAdd N = L := by
    funext j
    simp [Fin.append_right]
  have key : ∀ W : Ideal (MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
      (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) (specialIdeal W) d (Fin.append x L)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) (Equiv.refl _) (Fin.append x L) rfl hH W]
    simp only [Equiv.coe_refl, rename_id_apply]
    rw [plainPolynomialPairNumber.classNum_mul_tail _ L _ hnat]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [plainPairNumber.classNum_rename _ (Fin.castAdd_injective _ _), hcast]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [key, cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem main : ChernClassOnFlagPair.Statement :=
  ChernClassOnFlagPair.proof
    (JoinPointFlagModel.proof FlagPairCharacterisation.proof JoinPointModel.proof
      JoinPointVerticalDivisor.proof)
    (JoinPointNumbers.proof JoinPointIdeal.proof JoinDivCycle.proof JoinVariety.proof
      JoinIntNum.proof PairNumberJoinLeft.verticalComponentFibre)
    GlobalTheory.T.flag_model_value_independent GlobalTheory.T.flag_model_root_independent plainPolynomialPairNumber.proof rootPolyNum
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute) dividedDifferenceExpansion.proof

end GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial
