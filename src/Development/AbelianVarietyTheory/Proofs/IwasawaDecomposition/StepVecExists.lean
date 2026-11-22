module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.DataExtra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceDatum

theorem stepVecExists : ∀ D : D7, StepVecExists D := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf
  have hinf := infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT) βS βT
  obtain ⟨f, h⟩ := exists_isThetaAt hf.1 hS hT (idemSum_mul_self he) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS ΛT hS hT _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ (LS.Pg ∪ Q)
      (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
        rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
          omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
  exact ⟨f, hf, e, he, h⟩

end GlobalTheory.PlaceDatum
