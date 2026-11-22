module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartsAll

open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

theorem exists_charts : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  intro D V v w h
  refine ⟨fun hs => (GlobalTheory.NoExcl.chart V h hs).1, fun hns => ?_⟩
  have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
  obtain ⟨w₀, hw₀⟩ := (hI.1 (GlobalTheory.VacCoef.isUnram_host D v)).resolve_left hns
  have h₀ : w₀.under (𝓞 D.host.F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw₀
  obtain rfl : w = w₀ := ((hI.2 w₀ h₀ hw₀).2.2.1 w).1 h
  obtain ⟨-, ⟨c₀, hc₀, -⟩, -, -, H⟩ := hI.2 w h hw₀
  have hfix : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw₀ h
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hfix
  have hv2 : Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
    rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 (by exact_mod_cast h2)
  obtain ⟨⟨ϖ, hU⟩, -⟩ := H c₀ hc₀
  refine ⟨hw₀, GlobalTheory.InertLoc.odd_of_v_two hU hv2, fun c hc => ?_⟩
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨e, he, -⟩ := (H c hc).2 V.rank V.gram (frameLat V) (GlobalTheory.NoExcl.isHermND_gram V) (frameLat_fg V)
    hspan (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨e, he⟩

end GlobalTheory.ChartsAll
