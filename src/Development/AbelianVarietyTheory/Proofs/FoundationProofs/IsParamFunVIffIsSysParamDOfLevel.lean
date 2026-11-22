module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin

@[expose] public section

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem isParamVec_iff_isSysParam (hJ : SphOff J χ Sb) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Sb)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : List ℤ → ℂ} (hc : ∀ d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c d • f) (B : Multiset ℂˣ) :
    IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) f B ↔
      IsSysParam D.sp.cm.sig V.rank h c B := by
  have hx : f ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (hf k hk)
  have hs := isEigenSys_of_heckeLin hJ hv h hx hc
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
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
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  exact ⟨hs.isSysParam, hs.isParamVec h0 hx
    (fun hv => (SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hv hd).imp fun _ he => he.1)
    fun hw τ hτ => ((((exists_isInertChart _ (isCMExt_host D) v).2 w h hw).2.2.2.2 τ hτ).2 _ _ _ hH hL.fg
      hspan hd).imp fun _ he => he.1⟩

theorem isParamFunV_iff_isSysParamD (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  forall₂_congr fun v hv => forall₂_congr fun w h => isParamVec_iff_isSysParam hJ hv h h0 (hf v hv) (hc w) (B w)

theorem isParamFunV_iff_isSysParamD_of_level (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  isParamFunV_iff_isSysParamD hJ h0 (fun _ hv _ hk => fixed_of_level hJ hv hf hk) hc B

variable {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}

theorem isParamFunV_iff_of_mem_partFull (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partFull θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B :=
  have h := (mem_partFull θ M J χ Sb c T).1 hT
  isParamFunV_iff_isSysParamD_of_level hJ h0 (((GlobalTheory.MultMem.mem_mult_iff ..).1 h.1).lev x)
    (fun P d R hR => h.2 P d R hR x) B

theorem param_iff_sysParam (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (B : Fam D.host.E) (hJ : SphOff J χ Sb) :
    (∀ f : GA D V → ℂ, f ≠ 0 →
      (∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g) →
      (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) →
      (IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B)) ∧
    ∀ (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S),
      ∀ T ∈ partFull θ M J χ Sb c, ∀ x : M.Vec, T x ≠ 0 →
        (IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B) :=
  ⟨fun _ h0 hf hc => isParamFunV_iff_isSysParamD hJ h0 hf hc B,
    fun _ _ _ _ hT _ h0 => isParamFunV_iff_of_mem_partFull hJ hT h0 B⟩

theorem sphOff_KsphC (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    SphOff (KsphC V ∅) (fun _ => 1) Sb := fun P _ => by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) P
  exact ⟨e, f, h, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

end GlobalTheory.LFun

end
