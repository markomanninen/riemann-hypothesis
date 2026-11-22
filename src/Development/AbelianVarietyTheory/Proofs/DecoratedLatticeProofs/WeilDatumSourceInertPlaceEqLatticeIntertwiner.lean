module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter

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

noncomputable section

namespace GlobalTheory.WeilAtPlaceSrc

open GlobalTheory.WeilAtPlace GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {lam : ℕ →* ℂ} {w₀ : 𝓞 D.host.E} {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}

theorem weilDatum_source_eq_scalar_smul_latticeIntertwiner (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) {g : GA D S} (hg : g ∈ GfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = c • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, 1) * o (g⁻¹, 1⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem (one_mem _)) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := h _ (hpres (g, 1) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, 1⁻¹) * (g, 1) : GA D S × GA D T) = 1 from inv_mul_cancel (g, (1 : GA D T)), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem exists_weilScalarCharacter_sourceFinitePart (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) :
    ∃ ν : GA D S →* Circle, ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f),
      om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  have hs := fun g : GA D S => weilDatum_source_eq_scalar_smul_latticeIntertwiner hψ hW hL hlam (pFin_mem S g)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun g => ⟨c g, mem_sphere_zero_iff_norm.2 (hc g)⟩) fun p q => Circle.ext ?_,
    fun g hg f hf => ?_⟩
  · show c (p * q) = c p * c q
    have e1 : (pFin S (p * q), (1 : GA D T)) = (pFin S p, 1) * (pFin S q, 1) :=
      Prod.ext (map_mul _ _ _) (one_mul _).symm
    have e2 := h (p * q) f hf
    rw [e1, map_mul, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (pFin S q, 1) ⟨f, hf⟩).2, smul_smul, map_mul,
      Module.End.mul_apply] at e2
    have e3 := smul_left_injective ℂ (hne ((pFin S p, 1) * (pFin S q, 1))) (a₁ := c q * c p) (a₂ := c (p * q)) (by
      simpa only [map_mul, Module.End.mul_apply] using e2)
    rw [← e3, mul_comm]
  · have e := h g f hf
    rwa [pFin_of_mem hg] at e

theorem weilScalar_source_eq_one_nonsplit_unramified (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om) {ν : GA D S →* Circle}
    (hν : ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) (uS : UnramAt ε χS)
    (uT : UnramAt ε χT) {g : GA D S} (hg : SuppPl ε S g) : ν g = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place D S ΛS hS v ε hv ν (fun k hk hst => ?_) g hg
  have hvac' : ∃ f, f ≠ 0 ∧ IsThetaFunO ψ S T f ∧ ∀ v η, NonSplitAt D v η →
      ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f := by
    obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
    obtain ⟨e, he, e0⟩ : ∃ e, Fixes (opF hψ.1 S T w₀) (latF S T ΛS ΛT) e ∧ e ≠ 0 := by
      by_contra hn
      push_neg at hn
      have : (⊤ : Submodule ℂ (thetaSub ψ S T)) ≤ ⊥ := by
        rw [← hL.span, Submodule.span_le]
        rintro _ ⟨x, e, he, rfl⟩
        rw [hn e he, map_zero]
        exact zero_mem _
      exact f0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 (this (Submodule.mem_top (x := ⟨f, hf⟩)))))
    refine ⟨e, fun h0 => e0 (Subtype.ext h0), e.2, fun v η hv u hu => ?_⟩
    obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
    have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
    let a : XF S T := XF.mk u (GlobalTheory.SplitScalar.latO_fin hu')
    have ha : a ∈ latF S T ΛS ΛT := hu'
    have e0 : algebraMap (AF D.host.F) (AE D) η • u = u :=
      GlobalTheory.FinWeilForm.placeIdem_smul_self hv.1 hu
    have e1 : a = 2 • (b • a) := by
      rw [two_nsmul, ← add_smul, ← two_mul, hb']
      exact XF.ext e0.symm
    have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
    have h1 := congrArg Subtype.val (he a ha)
    rw [coe_opF] at h1
    have h2 : phase ψ w₀ a = 1 := by rw [e1]; exact phase_two hL.sd w₀ e2
    rwa [h2, one_smul] at h1
  obtain ⟨f₀, f0, hf₀, hvac⟩ := hvac'
  have hfix := hvac v ε hv
  have hst' := GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices D S T ΛS ΛT hS hT v ε hv.1 k 1 hst
    (fun y => by rw [GlobalTheory.FinWeilForm.finMat_one, Matrix.one_mulVec])
  have s1 : SuppPl ε T (1 : GA D T) := fun i j => by
    rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have a := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hψ S T ΛS ΛT hS hT χS χT om
    ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩) hW v ε hv uS uT k 1 hk s1 hst'
    f₀ hf₀ hfix
  have b := hL.inert hv hk s1 (fun u hu => (hst' u).1 hu) ⟨f₀, hf₀⟩ hfix
  have hkf : k ∈ GfC S := GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hv.1).1 hk
  have c := hν k hkf f₀ hf₀
  rw [a, b] at c
  exact Circle.ext (smul_left_injective ℂ f0 (c.symm.trans (one_smul ℂ f₀).symm))

end GlobalTheory.WeilAtPlaceSrc

end

theorem GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ (a : Gv S v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), om (embV S v a, 1) f = (Om (embV S v a, 1) f : WO S T → ℂ) := by
  intro D ψ S T χS χT om hW hψ lam w₀ Om hL hlam v w h hi uS uT a f
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ν, hν⟩ := GlobalTheory.WeilAtPlaceSrc.exists_weilScalarCharacter_sourceFinitePart hψ hW hL hlam
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hsu : GlobalTheory.WeilParts.SuppPl ε S (embV S v a) := (Supp.suppF_iff_of_isPrimeIdem S hp h _).2 ⟨a, rfl⟩
  have hk : embV S v a ∈ GfC S :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hns.1).1 hsu
  have e1 := GlobalTheory.WeilAtPlaceSrc.weilScalar_source_eq_one_nonsplit_unramified hψ hW (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat S)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat T) hL hν hns
    (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uS) (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uT) hsu
  have e2 := hν _ hk f.1 f.2
  rw [e1, Circle.coe_one, one_smul] at e2
  exact e2
