module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSRIffIsKS
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRingStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
open GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlagTan

open TensorProduct GlobalTheory.Frames GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem IsKSR.baseChangeForKSFamily (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ GlobalTheory.DeRham.epsRed S = GlobalTheory.DeRham.epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ GlobalTheory.DeRham.epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (GlobalTheory.DeRham.epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1] <;> rfl
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp


end GlobalTheory.FlagTan

namespace GlobalTheory.KSFam

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  rw [embK_coe, embK_coe]
  show starRingEnd ℂ (τ ((H.bar z : 𝓞 E) : E)) = τ (z : E)
  rw [H.9 z, NumberField.IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem ksFamily : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (Formalism.L2.Pj.dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  intro E _ _ _ H Dw l Xo c hP S _ _ y x' h1 h2
  suffices hM : ∃ M, GlobalTheory.FlagTan.IsKSR (psiSet H) y x' M by
    obtain ⟨M, hM⟩ := hM
    refine ⟨M, fun K _ _ ψ y' hy => GlobalTheory.FlagTan.isKSR_iff_isKS.mp ?_⟩
    exact GlobalTheory.FlagTan.IsKSR.baseChangeForKSFamily hP hy hM

  let : GrpObj ((Over.pullback x').obj Xo.univ.t.G) := Functor.grpObjObj (F := Over.pullback x')
  let : GrpObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    Functor.grpObjObj (F := Over.pullback (GlobalTheory.DeRham.epsRed S))
  have hA' := isGrpPullback_pullback Xo.univ.t.G x'
  have hi := isGrpPullback_pullback ((Over.pullback x').obj Xo.univ.t.G) (GlobalTheory.DeRham.epsRed S)
  have hA : IsGrpPullback ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G))
      Xo.univ.t.G y.x (pullback.fst _ _ ≫ pullback.fst _ _) := (hi.comp hA').congr h2 rfl
  have : IsCommMonObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hA
  have hab := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hsm := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA'
  have hab0 := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA
  have hsm' : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback x').obj Xo.univ.t.G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm
  have hsm0 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm'

  obtain ⟨ψ, hpol, hiso, hperf, hmax⟩ := GlobalTheory.T.exists_polarization_form_isotropic_filtration hP Xo hA

  obtain ⟨a', ha'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hA'
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a' hi
  have haπ : ∀ z, (a.act z).left ≫ (pullback.fst _ _ ≫ pullback.fst _ _) =
      (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (Xo.univ.t.act.act z).left := by
    intro z
    rw [← Category.assoc, ha z, Category.assoc, ha' z, Category.assoc]
  have hadj := GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point hP Xo hA a haπ hpol

  obtain ⟨ub, hub1, hubT, hubE, hubS⟩ := GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing y hA a haπ
  have hex : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), ∃ h, IsLieImage h (ub k.1 k.2) := fun k =>
    (hP.2.1 S _ _ hab0 hsm0).1.2 _ (hubT k.1 k.2)
  choose hb hhb using hex
  obtain ⟨hspan, hlin⟩ := GlobalTheory.T.grp_pullback_basis_lift_compatible hP y hA ub hub1 hb hhb
  have hreg := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing hP hi hab' hsm'
  have hcomp := fun z f w (e : IsKSValue hi f w) => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hi a a' ha z e
  have heig : ∀ (k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ))) (z : 𝓞 E),
      act (dp0 S) (𝟙 _) a z (hb k) - (algebraMap c.F S).comp (embK c k.1) z • hb k ∈
        Fil ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) := by
    intro k z
    have := a.hom z
    have e1 := (hhb k).push (a.act z)
    rw [hubE] at e1
    rw [act_apply]
    exact e1.sub_mem ((hhb k).smul _)
  have key : ∀ (τ : psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → S, ∃ w,
      IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hi ψ hb ⟨conjEmb τ.1, j⟩ w := fun τ j =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring hi a (fun z => H.bar z) ψ hiso hmax hperf hadj hreg hcomp
      (fun σ => (algebraMap c.F S).comp (embK c σ)) ub hb hspan hlin heig hubS τ.1 (conjEmb τ.1)
      (fun z => by simp only [RingHom.comp_apply, conj_embK']) j
  choose cf hcf using key
  exact ⟨fun k => cf k.1 k.2.1 k.2.2, _, inferInstance, _, inferInstance, _, _, _, hi, ψ, ub, hb, hA, hA', rfl, hpol,
    hub1, fun σ k => hhb ⟨σ, k⟩, fun τ j => hcf τ j⟩

end GlobalTheory.KSFam
