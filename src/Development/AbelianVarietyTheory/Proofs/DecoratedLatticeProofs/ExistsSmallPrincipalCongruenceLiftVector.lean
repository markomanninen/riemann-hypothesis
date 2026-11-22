module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCFrameLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SmallEx

theorem exists_isVacO {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := Formalism.IndefR.Datum.measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

theorem exists_small_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∃ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) ∧ IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f := by
  classical
  intro D ψ θ A H χA om sA sH hθ _ hW hA hH _ β Z hP
  have dA := GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat A
  have dH := GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat H
  have hspan : Submodule.span D.host.E (frameLat H : Set (Fin H.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (H.L0 : Set H.V) = ⊤ := by
      let W := Submodule.span D.host.E (H.L0 : Set H.V)
      change W = ⊤
      by_contra h
      let e : H.V ≃ₗ⋆[D.host.E] H.V :=
        (H.frame.equivFun.trans (starLinearEquiv D.host.E)).trans H.frame.equivFun.symm
      let g : H.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (H.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E H.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ H.L0 := by
        rw [← H.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : H.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : H.hT y (e x) = 0 := by
          rw [(H.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] H.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict H.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) H.L0 := Module.Finite.iff_fg.mpr H.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat H : Set (Fin H.rank → D.host.E)) =
        H.frame.equivFun.toLinearMap '' (H.L0 : Set H.V) :=
      (H.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨βH, hβH⟩ := GlobalTheory.AdelicFrame.exists_isFrame (F := D.host.F) (frameLat H) dH.1.fg hspan
  obtain ⟨f₀, hf₀⟩ := exists_isVacO ψ θ hW.std hθ A H sA sH hA hH _ _ dA dH
  have hsp : ∃ e : AE D, IsIdemSum e ((prinDat A Z).Pg ∪ ∅) := by
    obtain ⟨e, he⟩ := hP.idem
    exact ⟨e, by rw [Finset.union_empty]; exact he⟩
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.stepVecExists D ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z)
    (fun _ => 1) ∅ (fun _ => 1) dA dH hP.frame hβH (Finset.disjoint_empty_right _) hsp f₀ hf₀
  exact ⟨βH, f₀, f, hβH, hf⟩

end GlobalTheory.Core.Rk.SmallEx

end
