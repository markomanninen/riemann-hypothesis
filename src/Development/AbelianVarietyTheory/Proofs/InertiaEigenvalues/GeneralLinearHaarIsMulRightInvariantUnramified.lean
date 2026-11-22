module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfModular

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem gl_lc_sc (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ SecondCountableTopology (GL (Fin r) F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem gl_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  intro F E _ _ _ _ hU r M
  haveI : LocallyCompactSpace F := hU.lcF
  obtain ⟨h1, h2⟩ := gl_lc_sc F r
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  have hmod : ∀ a : GL (Fin r) F, Measure.modularCharacterFun a = 1 := by
    intro a
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center
      (Measure.modularCharacter : GL (Fin r) F →* NNReal) (fun z hz => ?_) a
    change Measure.modularCharacterFun z = 1
    have e : Measure.map (fun x : GL (Fin r) F => x * z)
        (Measure.haar : Measure (GL (Fin r) F)) = Measure.haar := by
      rw [show (fun x : GL (Fin r) F => x * z) = fun x => z * x from
        funext fun x => (hz x).symm, map_mul_left_eq_self]
    rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (GL (Fin r) F)) z]
    simp only [e, Measure.haarScalarFactor_self]
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, hmod, one_smul]

end GlobalTheory.JR
