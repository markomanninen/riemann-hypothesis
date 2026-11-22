module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TrPlus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.relKill_single {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A)
    (g : G) (a : A) : W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single g a) = a • W.mat ρ g := by
  ext i j
  simp [W.GDet.repAlg]

private theorem UpperTheory.V.Ws.Eb.relKill_push {R A G : Type} [CommRing R] [CommRing A] [Group G] {n : ℕ}
    (D : W.GDet n R G) (f : R →+* A) (ρ : G →* GL (Fin n) A) (hρ : Full ρ) (hD : D.map f = W.GDet.ofRep (W.mat ρ))
    (z : MonoidAlgebra R G) (hz : ∀ h : G, D.tr (MonoidAlgebra.single h 1 * z) = 0) :
    W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.mapRingHom G f z) = 0 := by
  refine (trPlus ρ hρ).1 (MonoidAlgebra.mapRingHom G f z) (fun g' => ?_)
  rw [← hD]
  have e : MonoidAlgebra.single g' (1 : A) * MonoidAlgebra.mapRingHom G f z =
      MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g' 1 * z) := by
    rw [map_mul]
    congr 1
    simp [MonoidAlgebra.mapRingHom]
  have hchi : ∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
    intro y
    have he : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) =
        MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
      rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
        ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
    show (D.map f).D A[X] _ = _
    rw [he]
    let : Algebra R A[X] := ((algebraMap A A[X]).comp f).toAlgebra
    have hc : ∀ a : R, Polynomial.mapRingHom f (algebraMap R R[X] a) = algebraMap R A[X] a := by
      intro a
      change Polynomial.map f (C a) = C (f a)
      exact Polynomial.map_C f
    exact D.nat R[X] A[X] { Polynomial.mapRingHom f with commutes' := hc } _
  have hmap : ∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
    intro i y
    simp only [W.GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  rw [e, W.GDet.tr.eq_1, hmap 1, ← W.GDet.tr.eq_1, hz g', map_zero]

theorem UpperTheory.V.Ws.Eb.relKill :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        (∀ v (g : Fin n → F.Gv v), (List.ofFn fun i => W.mat ρ (F.φ v (g i)) - algebraMap A _ (f (B.u.ψ v i (g i) : B.Bˣ))).prod = 0) ∧ ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 := by
  intro l _ F c n r B A _ _ f ρ hρ hD
  have key : ∀ z : MonoidAlgebra B.B F.G₀, (∀ h : F.G₀, B.u.D.tr (MonoidAlgebra.single h 1 * z) = 0) →
      W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.mapRingHom F.G₀ (f : B.B →+* A) z) = 0 :=
    fun z hz => relKill_push B.u.D (f : B.B →+* A) ρ hρ hD z hz
  have hsing : ∀ (x : F.G₀) (b : B.B), W.GDet.repAlg (W.mat ρ) A
      (MonoidAlgebra.mapRingHom F.G₀ (f : B.B →+* A) (MonoidAlgebra.single x b)) = (f b) • W.mat ρ x := by
    intro x b
    rw [← relKill_single]
    congr 1
    simp [MonoidAlgebra.mapRingHom]
  refine ⟨fun v g => ?_, fun u g hg => ?_⟩
  · have h0 := key _ (B.u.Ord v g)
    rw [W.GFrame.oEl.eq_1, map_list_prod, map_list_prod, List.map_map, List.map_ofFn] at h0
    simpa only [Function.comp_def, map_sub, hsing, map_one, one_smul,
      Algebra.algebraMap_eq_smul_one] using h0
  · have h0 := key _ (fun h => B.u.I u g hg h)
    simp only [map_sub, hsing, map_one, one_smul, sub_eq_zero] at h0
    exact Units.ext h0
