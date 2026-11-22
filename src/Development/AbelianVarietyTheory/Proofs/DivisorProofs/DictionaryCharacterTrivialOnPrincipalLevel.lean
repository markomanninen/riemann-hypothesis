module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneAddSubOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MuLevel

theorem det_cong_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : N ≠ 0) (k : GA D V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ w ∈ intAE D, (finHom V k).1.det - 1 = N • w := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  rw [hL] at hk
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F L hfg hsp N hN _ hk


set_option maxHeartbeats 1000000 in
theorem exists_root_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : Odd N) (k : GA D V) (hf : k ∈ GfC V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ x : (AE D)ˣ, IsDetRoot V k x ∧ FinUnit x ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y := by
  obtain ⟨w, hw, hwe⟩ := det_cong_of_level V N hN.pos.ne' k hk
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ?_, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, p, hp, hY2 ▸ hpe⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have h1 : infHom V k = 1 := hf
  have hs : infPart D (sigR (AF D.host.F) D.sp.cm.sig (Y : AE D)) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (Y : AE D)) := GlobalTheory.DetRootCong.map_sigR _ _ _
  refine e.injective (Prod.ext ?_ ?_)
  · rw [he1, he1, RingHom.map_mul, hs, ← hdet', h1, hY1, RingHom.map_one, mul_one]
    exact Matrix.det_one.symm
  · have hs' := GlobalTheory.DetRootCong.finPart_sigR D (Y : AE D)
    rw [hY2] at hs'
    rw [hdet, ← hs', ← RingHom.map_mul] at hroot
    exact (he2 _).trans ((hY2.trans hroot).trans (he2 _).symm)

theorem exists_ext {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : K →+* ℂ) :
    ∃ τ : L →+* ℂ, τ.comp (algebraMap K L) = σ := by
  letI : Algebra K ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩


set_option maxHeartbeats 1000000 in
theorem mu_eq_one_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL h _ i σ hσ _ k hk
  have hj := inR i
  obtain ⟨τ, rfl⟩ := exists_ext (L := D.what₂.LL) σ
  obtain ⟨hf, hk'⟩ := (h.laws.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := h.laws.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨x, hx, hu, hc⟩ := exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 i
  have h1 : R.mu0 ((i : ℕ) + 1) x = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hL.mu0 i) hm.tame _ (fun P hP => hm.unr P fun a ha => hP ?_) x hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  obtain ⟨y, hy1, hy2⟩ := (h.chiR i τ hσ).2.2.2.1 x hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL y = 1 :=
    D.what₂.embLL.injective (by rw [← hy1, h1, map_one, Circle.coe_one])
  rw [(h.laws.muVal _ hj _ hσ).2 k x hx, hy2, h2, map_one]

end GlobalTheory.MuLevel
