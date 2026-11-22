module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecOK

theorem stepVec_exists_vac : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → (∃ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) ∧ ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → IsThetaFunO c.ψ s.V s'.V f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO c.ψ s.V s'.V) c.θ τ (cplxO (cart s.M τ) (cart s'.M τ)) f) ∧ ∀ φ, IsThetaFunO c.ψ s.V s'.V (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f φ) := open GlobalTheory.PlaceDatum in by
  classical
  intro D c hc k s s' hs hs'
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + (k : ℕ) * D.R.t ≤ D.R.r + ((k : ℕ) + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  refine ⟨?_, fun ξ f₀ f h => ?_⟩
  · obtain ⟨f₀, hf₀⟩ := GlobalTheory.VacuumO.vacExists D c.ψ c.θ hc.std hc.inf s.V s'.V (cart s.M) (cart s'.M) hs.sigOK hs'.sigOK
      (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) s.Λ s'.Λ hs.selfDual hs'.selfDual
    obtain ⟨_, ξL, hL⟩ := hs.lev
    have hsp : ∃ e : AE D, IsIdemSum e (s.L.Pg ∪ ∅) := by
      obtain ⟨e, he⟩ := hc.split
      refine ⟨e, ?_⟩
      rw [Finset.union_empty, hL]
      exact he
    have hstep : StepVecExists D := by
      intro ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf
      have hinf := infPart_idemSum he
      obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
        (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) βS βT
      obtain ⟨f, h⟩ := exists_isThetaAt hf.1 hS hT (idemSum_mul_self he) hinf
        (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS ΛT hS hT _ e he f₀ hf.2.theta hf.2.lat).1
        (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
          ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ (LS.Pg ∪ Q)
          (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
            rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
              omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
      exact ⟨f, hf, e, he, h⟩
    obtain ⟨f, hf⟩ := hstep c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L
      (c.chi ((k : ℕ) + 1)) ∅ 1 hs.selfDual hs'.selfDual hs.frame hs'.frame (Finset.disjoint_empty_right _) hsp f₀ hf₀
    exact ⟨1, f₀, f, hf⟩
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr h
    exact ⟨h1, h2, h3, fun φ => GlobalTheory.FockTheta.ptStable D c.ψ c.θ hc.std hc.inf s.V s'.V _ _ _ _ f φ h1⟩

end GlobalTheory.ChainOnto.StepVecOK
