module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictEqInvLocalArtinMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralIffSpectralNormLeOne
public import GroundTheory.LocalFields.MainTheorem
public import GroundTheory.GlobalFields.CompletionAtPlace

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.ArtinNormU

theorem localArtin_normU : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' _ a a' ha ha' g g' hgg
  classical
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v'.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (v'.adicCompletion L)).injective
  haveI : IsSepClosure (v'.adicCompletion L) (Kbar v') := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.IsSeparable (v.adicCompletion K) (v'.adicCompletion L) := inferInstance
  haveI : IsSepClosure (v.adicCompletion K) (Kbar v') :=
    isSepClosure_of_isSeparable (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb L Ω A v' h'
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc L Ω A v' h' ι' hι'
  let gL : GalLoc v' := θ ⟨g', Weil_le_Dec h' g'.2⟩
  have hgL : Lifts ι' gL (g' : G L Ω) := hθ _
  let gK : Kbar v' ≃ₐ[v.adicCompletion K] Kbar v' := gL.restrictScalars (v.adicCompletion K)
  have hgK : ∀ z : Ω, gK (ι'.toRingHom z) = ι'.toRingHom ((g : G K Ω) z) := fun z => by
    change gL (ι' z) = ι' _
    rw [hgL z, hgg z]
  have hj : ∀ x : K, ι'.toRingHom (algebraMap K Ω x) =
      algebraMap (v.adicCompletion K) (Kbar v') (algebraMap K (v.adicCompletion K) x) := fun x => by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    change ι' (algebraMap L Ω _) = _
    rw [ι'.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v'),
      GroundTheory.Global.AdicLiesOver.algebraMap_eq, GroundTheory.Global.adicCompletionMap_algebraMap,
      ← IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v')]
  let b : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb : ∀ x, (b : Kbar v ≃+* Kbar v') (algebraMap _ (Kbar v) x) =
      algebraMap (v'.adicCompletion L) (Kbar v') (GroundTheory.Global.adicCompletionMap v v' x) := fun x => by
    change b _ = _
    rw [b.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')]
    rfl
  have hc : (algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
    exact (b.commutes _).symm
  have hA : ∀ z : Ω, z ∈ A ↔ ((algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).IsIntegralElem (ι'.toRingHom z) := fun z => by
    have e := GlobalTheory.ClosureIso.isIntegral_map_iff (GroundTheory.Global.adicCompletionMap v v')
      (GroundTheory.Global.continuous_adicCompletionMap v v') (b : Kbar v ≃+* Kbar v') hb (b.symm (ι' z))
    have e2 : (b : Kbar v ≃+* Kbar v') (b.symm (ι' z)) = ι' z := b.apply_symm_apply _
    rw [e2] at e
    rw [hι' z, e, hc]
    change _ ↔ ((b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v))).IsIntegralElem (ι' z)
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      have := congrArg (b : Kbar v →+* Kbar v') hp'
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (b : Kbar v →+* Kbar v').injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _]
      exact hp'
  have restrict_local : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
      [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
      ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
        AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
          (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
    intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
    have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
      GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
    obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
    let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
    have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
    have e2 : ψ σ = g := by
      have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
        have := hl (θ.symm g)
        rw [θ.apply_symm_apply] at this
        exact Subtype.ext (this.eq hg)
      show θ _ = g
      rw [← e, θ.apply_symm_apply]
    let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
    have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
        (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
        restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
      restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
    have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
        [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
        a τ ∈ (normUnits (w.adicCompletion E) L).range →
          restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
      have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
      rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
      exact this
    let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
    have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
    have hker : a'.ker ≤ r.ker := fun τ hτ => by
      have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
      refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
      rw [map_one]
      exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
    let b := a'.liftOfSurjective ha' ⟨r, hker⟩
    have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
      MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
    have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
      refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
      · obtain ⟨τ, rfl⟩ := ha' π
        have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
        rw [ha.ord_eq, deg_inv, neg_neg] at h1
        have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
        change restrictAb _ _ (b (a τ)⁻¹) = _
        rw [hb, hr]
        refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
        rw [unramifiedDegree_eq_ofAdd_one_iff]
        rintro ξ ⟨n, hn, hξ⟩
        have hq : Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation (w.adicCompletion E)).integer) = normV w := resCard_eq_normV w
        rw [hq] at hξ ⊢
        refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
        have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
          (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (one_lt_normV w)))).symm
        rw [h2, pow_succ, hξ, one_mul]
      · obtain ⟨τ, rfl⟩ := ha' x
        change restrictAb _ _ (b (a τ)⁻¹) = _
        rw [hb]
        exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
    rw [← map_inv, ← hbφ, hb, ← e2]
    rfl
  
  have HK : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK =
      (localArtinMap (v.adicCompletion K) (Kbar v') (a g))⁻¹ := by
    have : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have : IsSepClosure (v.adicCompletion K) (Kbar v) := ⟨inferInstance, inferInstance⟩
    let ε : (Kbar v') ≃ₐ[v.adicCompletion K] Kbar v := IsSepClosure.equiv (v.adicCompletion K) (Kbar v') (Kbar v)
    let ι : Ω →ₐ[K] Kbar v :=
      { (ε : (Kbar v') →+* Kbar v).comp ι'.toRingHom with
        commutes' := fun x => by
          change ε (ι'.toRingHom (algebraMap K Ω x)) = _
          rw [hj, ε.commutes, IsScalarTower.algebraMap_apply K (v.adicCompletion K) (Kbar v)] }
    have hιz : ∀ z, ι z = ε (ι'.toRingHom z) := fun _ => rfl
    have hc : (ε : (Kbar v') →+* Kbar v).comp ((algebraMap (v.adicCompletion K) (Kbar v')).comp
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))) =
        algebraMap (v.adicCompletionIntegers K) (Kbar v) := RingHom.ext fun x => by
      rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
      exact ε.commutes _
    have hι : IsLocEmb A v ι := fun z => by
      rw [hA, hιz]
      constructor
      · rintro ⟨p, hp, hp'⟩
        refine ⟨p, hp, ?_⟩
        rw [← hc]
        have := congrArg (ε : (Kbar v') →+* Kbar v) hp'
        rwa [Polynomial.hom_eval₂, map_zero] at this
      · rintro ⟨p, hp, hp'⟩
        refine ⟨p, hp, (ε : (Kbar v') →+* Kbar v).injective ?_⟩
        rw [Polynomial.hom_eval₂, map_zero, hc]
        exact hp'
    let gK' : GalLoc v := ε.symm.trans (gK.trans ε)
    have hg' : Lifts ι gK' g := fun z => by
      change ε (gK (ε.symm (ε (ι'.toRingHom z)))) = ε (ι'.toRingHom _)
      rw [ε.symm_apply_apply, hgK]
    have H := restrict_local K Ω A v h ι hι a ha g gK' hg'
    have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK =
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g))⁻¹ := by
      rw [← map_inv] at H ⊢
      ext y
      have h1 := localArtinMap_transport (RingEquiv.refl (v.adicCompletion K)) (fun _ _ => Iff.rfl)
        (ε : (Kbar v') ≃+* Kbar v) (fun x => ε.commutes x) (a g)⁻¹ y.2
      have h2 : Units.map (RingEquiv.refl (v.adicCompletion K)).toRingHom.toMonoidHom (a g)⁻¹ = (a g)⁻¹ :=
        Units.ext rfl
      rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
      rw [AlgEquiv.restrictNormalHom_apply]
      apply ε.injective
      refine Eq.trans ?_ h1.symm
      change _ = ε (gK (ε.symm (ε y)))
      rw [ε.symm_apply_apply]
    exact H1
  have HL : ∀ (z : Kbar v') (hz : z ∈ maximalAbelianExtension (v'.adicCompletion L) (Kbar v')),
      gL ((localArtinMap (v'.adicCompletion L) (Kbar v') (a' g') ⟨z, hz⟩ :
        maximalAbelianExtension (v'.adicCompletion L) (Kbar v')) : Kbar v') = z := by
    intro z hz
    have H := restrict_local L Ω A v' h' ι' hι' a' ha' g' gL hgL
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v'.adicCompletion L) (Kbar v')) gL
        (localArtinMap (v'.adicCompletion L) (Kbar v') (a' g') ⟨z, hz⟩) = ⟨z, hz⟩ := by
      rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v'.adicCompletion L) (Kbar v') => (y : Kbar v')) e
    simpa only [AlgEquiv.restrictNormalHom_apply] using e2
  have kK : ∀ (y : Kbar v') (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (Kbar v')),
      gK ((localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩ :
        maximalAbelianExtension (v.adicCompletion K) (Kbar v')) : Kbar v') = y := fun y hy => by
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩) = ⟨y, hy⟩ := by
      rw [HK, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v.adicCompletion K) (Kbar v') => (y : Kbar v')) e
    simp only [AlgEquiv.restrictNormalHom_apply] at e2
    exact e2
  have key : localArtinMap (v.adicCompletion K) (Kbar v') (a g) =
      localArtinMap (v.adicCompletion K) (Kbar v') (normUnits (v.adicCompletion K) (v'.adicCompletion L) (a' g')) := by
    refine AlgEquiv.ext fun y => Subtype.ext ?_
    have hN := localArtinMap_norm (K := v.adicCompletion K) (K' := v'.adicCompletion L) (Ω := Kbar v') (a' g') y.2
    apply gK.injective
    rw [kK y y.2]
    change (y : Kbar v') = gL _
    rw [← hN, HL]
  exact injective_localArtinMap key

end GlobalTheory.ArtinNormU
