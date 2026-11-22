module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CosetGroupMembership
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CosetGroupEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

@[expose] public section

noncomputable section

namespace GlobalTheory.Proof.TotallyDefiniteMass

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

theorem mass_tMap {K V V' : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h' (Formalism.MainNotions.StandardLattice.tMap e L) := by
  by_cases hex : ∃ s', Formalism.ThetaLiftIndependence.IsClassReps h' (Formalism.MainNotions.StandardLattice.tMap e L) s'
  · refine Formalism.MainNotions.StandardLattice.mass_transport e he L hex fun s hs => ?_
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h' _ hex]
    apply Complex.ofReal_injective
    rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
    exact Formalism.ThetaLiftIndependence.latLiftIndep K V' h' _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
  · have hex' : ¬ ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := fun ⟨s, hs⟩ => hex ⟨_, Formalism.MainNotions.StandardLattice.tMap_reps e he L s hs⟩
    unfold Formalism.HermitianLatticesTheory.mass
    rw [dite_eq_right hex, dite_eq_right hex']

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isTotDef_gram (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef) :
    IsTotDef hc.sig S.gram := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  refine ⟨hc.totReal, fun ι => ?_⟩
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let τ : E →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine (Formalism.UG.Final.DefSig F E _ hc.sig S.gram ι (τ : E →+* ℂ) (RingHom.ext (hσ.2.2.2 (τ : E →+* ℂ)))
    (RingHom.ext fun a => τ.commutes a) (fun e he => (hc.fixed e).1 he)
    (Matrix.ext fun i j => (hJ S).1 i j) (hJ S).2.isUnit).2 (Or.inl ?_)
  have := h1 (τ : E →+* ℂ)
  rw [h2] at this
  simpa using this

private theorem span_eq_top_of_unimodular (S : HSpace E) (N : Submodule (𝓞 E) S.V)
    (hN : N.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT N) :
    Submodule.span E (N : Set S.V) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg S.frame
  let μ := ∑ j, star (φ (S.frame j)) • bs j
  have hμ : ∀ v, S.hT μ v = φ v := by
    have key : S.hT μ = φ := by
      apply S.frame.ext
      intro i
      dsimp only [μ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      have hs : ∀ j, S.hT (star (φ (S.frame j)) • bs j) (S.frame i) =
          φ (S.frame j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
        congr 1
        rw [← S.herm.eq (S.frame i) (bs j), hbs]
        split_ifs <;> simp
      simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro v
    rw [key]
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : E) : a • μ ∈ N := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT N
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ N.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hN.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]

theorem cosetSum (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef)
    (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT N) :
    CosetGroupMembership.CosetSum (UFin hc S) (CosetGroupMembership.stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N) := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  have hd := isTotDef_gram hc S h1 h2
  have hτ : ∀ τ : E →+* ℂ, τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (hc.sig : E →+* E) S.gram := Matrix.ext fun i j => (hJ S).1 i j
  have hL : Submodule.IsLattice E (crdLat S N) := Formalism.MainNotions.StandardLattice.tMap_lattice (crd S) N hN
  have hspan : Submodule.span E (crdLat S N : Set (Fin S.rank → E)) = ⊤ := by
    rw [← LinearEquiv.range (crd S), ← Submodule.map_top, ← span_eq_top_of_unimodular S N hN.fg hU,
      Submodule.map_span]
    congr 1
  have hf : Module.Finite (𝓞 E) (crdLat S N) := Module.Finite.iff_fg.2 hL.fg
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hm := GlobalTheory.Mass.classMass_lattice_eq_genus_mass hσ (hJ S) hd hs (crdLat S N) hf hspan
  have ht : Formalism.HermitianLatticesTheory.mass S.hT N =
      Formalism.HermitianLatticesTheory.mass (formJ (hc.sig : E →+* E) hs S.gram 1 :
        (Fin S.rank → E) →ₗ⋆[E] (Fin S.rank → E) →ₗ[E] E) (crdLat S N) := by
    refine mass_tMap (crd S) (fun x y => ?_) N
    rw [hT_crd hc]
    change Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • S.gram) (crd S x) (crd S y) = _
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [one_smul, smul_eq_mul, RingHom.id_apply]
    change star _ * _ = star _ * _ * _
    ring
  rw [CosetGroupMembership.stabHat_eq]
  refine ⟨Formalism.UG.Final.ClassSetFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hspan,
    fun y => (CosetGroupEquiv.cosetGrpEquiv _ _ y).finite_iff.2
      (Formalism.UG.Final.AdelicStabFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hspan y),
    fun ι _ y hy => ?_⟩
  simp only [CosetGroupEquiv.card_cosetGrp]
  exact (GlobalTheory.Mass.classMass_eq_sum_of_bijective y hy).symm.trans (hm.trans ht.symm)

theorem generalForm : CosetGroupMembership.GeneralForm :=
  fun _ _ _ _ _ _ _ _ hc S h1 h2 N hN hU => cosetSum hc S h1 h2 N hN hU

theorem massAsCosetSum : CosetGroupMembership.MassAsCosetSum :=
  ⟨generalForm, CosetGroupEquiv.column_of_general generalForm⟩

end GlobalTheory.Proof.TotallyDefiniteMass

end
