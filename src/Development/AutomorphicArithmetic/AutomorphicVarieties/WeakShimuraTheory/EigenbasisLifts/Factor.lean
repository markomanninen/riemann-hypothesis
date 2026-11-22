module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TrPlus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem factor_chi {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem factor_abs {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have repAlg_single {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
      (g : K) (r : B) : W.GDet.repAlg R B (MonoidAlgebra.single g r) = r • (R g).map (algebraMap A B) := by
    unfold W.GDet.repAlg
    rw [MonoidAlgebra.lift_single]
    rfl
  have repAlg_map {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
      (y : MonoidAlgebra A K) :
      W.GDet.repAlg R B (MonoidAlgebra.mapRingHom K (algebraMap A B) y) = (W.GDet.repAlg R A y).map (algebraMap A B) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => simp [MonoidAlgebra.of_apply, repAlg_single]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      ext i j
      simp
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by rw [Algebra.smul_def]; rfl
      have hm : MonoidAlgebra.mapRingHom K (algebraMap A B) (MonoidAlgebra.single 1 r)
          = MonoidAlgebra.single 1 (algebraMap A B r) := by
        ext g
        simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, repAlg_single, repAlg_single, map_one]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have chi_eq {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A K) :
      (W.GDet.ofRep R).chi y = (W.GDet.repAlg R A y).charpoly := by
    unfold W.GDet.chi
    change (W.GDet.repAlg R A[X] _).det = _
    rw [← Polynomial.algebraMap_eq, map_sub, repAlg_single, repAlg_map, map_one]
    rw [Matrix.charpoly]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
  have tr_eq (y : MonoidAlgebra A H) :
      (W.GDet.ofRep (W.mat ρ)).tr y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold W.GDet.tr W.GDet.lam
    rw [chi_eq, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    ring
  have chi_single {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (g : K) :
      (W.GDet.ofRep R).chi (MonoidAlgebra.single g 1) = (R g).charpoly := by
    rw [chi_eq, repAlg_single]; simp
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, factor_chi]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [tr_eq _, tr_eq _] at e
      rw [tr_eq _, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, chi_single, chi_single, hm]

theorem UpperTheory.V.Ws.Eb.factor :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), 1 ≤ n → x.IsRep ρ → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) →
        ∃ ρ₀ : V.frame.G₀ →* GL (Fin n) (PadicAlgCl l), ρ₀.comp V.pr = ρ ∧ Full ρ₀ ∧ B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ₀) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hn hx hirr
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  exact factor_abs x.D V.pr hs ρ hn hF hx
