module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
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
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) hspan h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

end Zero

end GlobalTheory.NoExcl

end
