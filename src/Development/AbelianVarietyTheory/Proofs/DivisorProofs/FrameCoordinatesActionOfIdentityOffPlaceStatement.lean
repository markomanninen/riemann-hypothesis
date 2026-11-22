module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coordinates_action_of_identity_off_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
        (g : UA σ X.J) (h : UA σ W.J),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι →
        mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι →
        ∀ x, actAB (cA σ) (g, h) (GlobalTheory.InertLocFrame.xm ι PV PW x) =
          (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  first | exact @GlobalTheory.InertLocFrame.actAB_xm_frame | exact GlobalTheory.InertLocFrame.actAB_xm_frame | (intros; apply GlobalTheory.InertLocFrame.actAB_xm_frame <;> assumption)
