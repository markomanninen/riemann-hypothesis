module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval

@[expose] public section

open Polynomial UpperTheory.V.W

private theorem injTest_mvInj {A : Type} [CommRing A] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    (f : ∀ x, A →+* K x) (hf : ∀ a, (∀ x, f x a = 0) → a = 0) {σ : Type} (P Q : MvPolynomial σ A)
    (h : ∀ x, MvPolynomial.map (f x) P = MvPolynomial.map (f x) Q) : P = Q := by
  ext β
  rw [← sub_eq_zero]
  refine hf _ fun x => ?_
  have := congrArg (AddMonoidAlgebra.coeff · β) (h x)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this
  rw [map_sub, this, sub_self]

private theorem injTest_smul {R S G : Type} [CommRing R] [CommRing S] [Group G] (φ : R →+* S) (r : R)
    (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G φ (r • z) = φ r • MonoidAlgebra.mapRingHom G φ z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]
  | single g s => simp

private theorem injTest_comp {R S T G : Type} [CommRing R] [CommRing S] [CommRing T] [Group G]
    (φ : R →+* S) (ψ : S →+* T) (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G ψ (MonoidAlgebra.mapRingHom G φ z) = MonoidAlgebra.mapRingHom G (ψ.comp φ) z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp

theorem UpperTheory.V.AlgebraTools.Det.injTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) →
    (∀ D D' : GDet n A G, (∀ x, D.map (f x) = D'.map (f x)) → D = D') ∧
    (∀ (D : GDet n A G) (y : MonoidAlgebra A G), (∀ x, (D.map (f x)).Kills (MonoidAlgebra.mapRingHom G (f x) y)) → D.Kills y) := by
  intro n A G _ _ X K _ f hf
  have mapEval (D : GDet n A G) (x : X) {σ : Type} (z : MonoidAlgebra (MvPolynomial σ A) G) :
      (D.map (f x)).D (MvPolynomial σ (K x)) (MonoidAlgebra.mapRingHom G (MvPolynomial.map (f x)) z) =
        MvPolynomial.map (f x) (D.D (MvPolynomial σ A) z) := by
    let : Algebra A (MvPolynomial σ (K x)) := ((algebraMap (K x) (MvPolynomial σ (K x))).comp (f x)).toAlgebra
    exact D.nat _ _ { MvPolynomial.map (f x) with commutes' := fun a => MvPolynomial.map_C (f x) a } z
  have evalGen (B : Type) [CommRing B] [Algebra A B] {m : ℕ} (g : Fin m → G) (b : Fin m → B) :
      MonoidAlgebra.mapRingHom G (MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B)
          (GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)) =
        ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
    simp only [GDet.gen, map_sum, injTest_smul, RingHom.coe_coe, MvPolynomial.aeval_X]
    simp
  refine ⟨fun D D' h => ?_, fun D y h => ?_⟩
  · apply GDet.ext
    intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    let z := GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)
    have hz : D.D (MvPolynomial (Fin m) A) z = D'.D (MvPolynomial (Fin m) A) z := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, ← mapEval D' x z, h x]
    rw [← evalGen B g b, D.nat, D'.nat, hz]
  · intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    set z : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
      1 + GDet.gen (fun j => MonoidAlgebra.single (g j) (1 : A)) * MonoidAlgebra.mapRingHom G MvPolynomial.C y with hz
    have h1 : D.D (MvPolynomial (Fin m) A) z = 1 := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, map_one, hz, map_add, map_one, map_mul, injTest_comp]
      have e : (MvPolynomial.map (f x) : MvPolynomial (Fin m) A →+* _).comp MvPolynomial.C =
          (algebraMap (K x) (MvPolynomial (Fin m) (K x))).comp (f x) := by
        ext a : 1
        simp
      rw [e, ← injTest_comp]
      exact h x _ _
    have h2 := D.nat _ B (MvPolynomial.aeval b) z
    have e : ((MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B) : MvPolynomial (Fin m) A →+* B).comp
        MvPolynomial.C = algebraMap A B := by
      ext a : 1
      simp
    rw [h1, map_one, hz, map_add, map_one, map_mul, injTest_comp, e, evalGen] at h2
    exact h2
