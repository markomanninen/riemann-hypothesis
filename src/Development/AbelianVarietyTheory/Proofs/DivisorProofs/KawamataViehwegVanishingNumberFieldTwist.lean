module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.VanishNumberField

open GlobalTheory.AbLaw

theorem subsingleton_of_tensor {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
    (h : Subsingleton (TensorProduct k E V)) : Subsingleton V := by
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial k E V)

theorem subsingleton_coh_of_pull {k E : Type} [Field k] [Field E] [Algebra k E] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X} [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ)
    (h : Subsingleton (coh (twist (structureModule X') (M.pull π)) n)) :
    Subsingleton (coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have cechIso {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      (N : LB Z) {κ : Type} [LinearOrder κ] (U : κ → Z.Opens) :
      letI := algebraΓOfHom g
      cechLB g N U ≅ cech R (LB.toMod N) ⊤ U := by
    letI := algebraΓOfHom g
    exact (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
      (M := SecOnR g N (⨅ i ∈ s, U i)) (M₂ := sectionsOn (LB.toMod N) (⊤ ⊓ ⨅ i ∈ s, U i))
      (SecOnR.restrict g N (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, U i) ≤ ⨅ i ∈ s, U i))
      (SecOnR.restrict_bijective g _ (le_inf le_top le_rfl)))
      fun {s t} ht x => (SecOnR.restrict_restrict g _ inf_le_right x).trans
        (SecOnR.restrict_restrict g inf_le_right (cechOpen_anti ⊤ U ht) x).symm)
  have cohEquiv {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      {N : LB Z} (hN : N.IsLB) {κ : Type} [LinearOrder κ] [Finite κ] {U : κ → Z.Opens}
      (hu : ⨆ i, U i = ⊤) (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (i : ℕ) :
      letI := algebraΓOfHom g
      Nonempty ((cechLB g N U).homology i ≃ₗ[R] coh (twist (structureModule Z) N) i) := by
    letI := algebraΓOfHom g
    haveI := LB.isQuasicoherent_toMod hN
    exact ⟨((HomologicalComplex.homologyFunctor _ _ i).mapIso (cechIso g N U)).toLinearEquiv ≪≫ₗ
      cechHEquivCoh R hu hU (LB.toMod N) i ≪≫ₗ (cohOn.mapIso R ⊤ i (Twist.unitTwistIso N)).symm⟩
  have homologyEquiv {R : Type} (O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
      (C : CochainComplex (ModuleCat.{0} R) ℕ) (i : ℕ) :
      Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
        C).homology i ≃ₗ[O] TensorProduct R O (C.homology i)) := by
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
    have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
    obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology i)
    exact ⟨((C.sc i).mapHomologyIso
      (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩
  obtain ⟨e₁⟩ := cohEquiv f hM hc hD' n
  obtain ⟨e₂⟩ := cohEquiv f' (LB.isLB_pull hM π) (U := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := homologyEquiv E (cechLB f M D) n
  have bcIso (g : k →+* E)
      (H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
      ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (cechLB f M D) ≅
        cechLB f' (M.pull π) (fun i => π ⁻¹ᵁ D i) := by
    letI := g.toAlgebra
    let φ : (secCube f M D ⋙ ModuleCat.extendScalars g) ⟶
        secCube f' (M.pull π) (fun i => π ⁻¹ᵁ D i) :=
      Cube.homMk (Fin m) E (fun s => SecOnR.baseChangeHom M H'.w _ _ (preimage_biInf D π s).ge)
        fun {s t} ht x => SecOnR.baseChangeHom_restrict H'.w (iInf_le_iInf_of_subset D ht)
          (iInf_le_iInf_of_subset (fun i => π ⁻¹ᵁ D i) ht) (preimage_biInf D π s).ge
          (preimage_biInf D π t).ge x
    exact @asIso _ _ _ _ (cechComparison (ModuleCat.extendScalars g) (secCube f M D))
      (isIso_cechComparison _ _) ≪≫
      @asIso _ _ _ _ (cechComplexMap φ)
        (isIso_cechComplexMap _ fun s hs => SecOnR.baseChangeHom_bijective hM H' (hD' s hs) (preimage_biInf D π s).symm)
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (bcIso (algebraMap k E) H)).toLinearEquiv
  have h₁ : Subsingleton (TensorProduct k E ((cechLB f M D).homology n)) :=
    (e₃.symm.toEquiv.trans (e₄.toEquiv.trans e₂.toEquiv)).subsingleton_congr.2 h
  exact e₁.symm.toEquiv.subsingleton_congr.2 (subsingleton_of_tensor h₁)

theorem topologicalKrullDim_eq_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [Nonempty Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y = D := by
  have key : topologicalKrullDim (Set.univ : Set Y) = D := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    replace hU : IsAffineOpen (X := Y) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)
  rw [← key]
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : Y → Y)) Topology.IsEmbedding.id Set.range_id).symm

theorem vanishFrom_adj : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  intro Q K _ _ G hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K (X := G.Y)) := hstr ▸ hV.proj
  haveI : IsProper (strHom K (X := G.Y)) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens G.LA (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens G.LA (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens G.LA (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens G.LA (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (G.isLB_adj j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((G.adj j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (G.isLB_adj j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add (f := _)]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB G.isLBA) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB G.isLBA,
          cls_tens G.isLBA (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (G.adj j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (G.isLB_adj j) q hKV
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (G.isLB_adj j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle G.LA)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

end GlobalTheory.HSCore.VanishNumberField
