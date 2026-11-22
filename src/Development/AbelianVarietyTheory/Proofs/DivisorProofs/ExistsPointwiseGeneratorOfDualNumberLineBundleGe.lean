module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointPreimageTopOfReduction

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem epsGen_epsEv_apply {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) e u = u.fst + u.snd * ptAlg (R := R) (D := DualNumber R) e DualNumber.eps := by
  simp [epsEv, DualNumber.lift_apply_apply]

theorem epsGen_epsEv_nat {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) (E := E') (spOver ψ ≫ e) (epsHom ψ u) = ψ (epsEv (R := R) e u) := by
  obtain ⟨h1, h2, -⟩ := dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ u
  simp only [epsGen_epsEv_apply, h1, h2, ptAlg_comp, AlgHom.comp_apply, map_add, map_mul]

theorem epsGen_spMap_eq {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (p : Sp E) :
    (spMap (epsEv (R := R) e : DualNumber E →+* E)).base p =
      (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p := by
  apply PrimeSpectrum.ext
  ext u
  have hc : ptAlg (R := R) (D := DualNumber R) (E := E) e DualNumber.eps ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, ← map_mul, DualNumber.eps_mul_eps, map_zero]; exact p.asIdeal.zero_mem)
  change epsEv (R := R) e u ∈ p.asIdeal ↔ u.fst ∈ p.asIdeal
  rw [epsGen_epsEv_apply]
  constructor
  · intro h
    have := p.asIdeal.sub_mem h (p.asIdeal.mul_mem_left u.snd hc)
    simpa using this
  · intro h
    exact p.asIdeal.add_mem h (p.asIdeal.mul_mem_left u.snd hc)

theorem epsGen_mem {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) {Y : Scheme.{0}}
    (y : Sp (DualNumber E) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (spMap (epsEv (R := R) e : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U) :
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (Set.mem_univ p)
  change y.base ((spMap (epsEv (R := R) e : DualNumber E →+* E)).base p) ∈ U at this
  change y.base ((spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p) ∈ U
  rwa [← epsGen_spMap_eq (R := R) e p]

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem epsGen_red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV (R := R) (D := E) v x =
      x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = (1 : SpAlg R R ⟶ B) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, spOver_left]
    refine hv.trans ?_
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    change η[B].left = spMap (RingHom.id R) ≫ η[B].left
    rw [Cris.spMap_id, Category.id_comp]
  rw [AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      ext a
      simp
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', MonObj.comp_one]

theorem epsGen_key (v : epsR R ⟶ B) {E : Type} [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) :
    z ≫ lift (fst A (epsR R)) (snd A (epsR R) ≫ v) =
      spOver (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp
        (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      simp [epsEv]
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp (EpsWeil.epsMap R E) =
        ptAlg (R := R) (D := DualNumber R) (E := E) (z ≫ snd A (epsR R)) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap, epsEv]
    rw [this, spOver_ptAlg, Category.assoc]

theorem exists_isPtGen_of_isEpsGen : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ T, IsEpsGen (R := R) (A := A) P v T →
    ∃ t, IsPtGen (R := R) P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  intro R _ A B _ _ P _ v hv T hT
  obtain ⟨T1, T2, T3⟩ := hT
  have memV : ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
      ⊤ ≤ (ptV (R := R) (D := E) v x).left ⁻¹ᵁ P.U i := by
    intro E _ _ x i h
    apply dualNumberPoint_preimage_top_of_reduction _ E (ptV (R := R) (D := E) v x).left (P.U i)
    have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
    rw [← epsGen_red_ptV (R := R) (E := E) hv x] at h1
    exact h1
  have memA : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) (i : P.ι),
      ⊤ ≤ (z ≫ CartesianMonoidalCategory.lift (fst A (epsR R)) (snd A (epsR R) ≫ v)).left ⁻¹ᵁ P.U i →
      ⊤ ≤ (z ≫ fst _ _).left ⁻¹ᵁ chartsA P i := by
    intro E _ _ z i h
    rw [epsGen_key (R := R) (E := E) v z, Over.comp_left, spOver_left] at h
    have h2 := epsGen_mem (R := R) (E := E) (z ≫ snd A (epsR R)) _ _ h
    have h3 : ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ P.U i := h2
    rw [epsGen_red_ptV hv] at h3
    exact h3
  refine ⟨fun E _ _ z i ↦ epsEv (R := R) (E := E) (z ≫ snd A (epsR R))
    (T E (z ≫ fst A (epsR R)) i), ?_, ?_, ?_⟩
  · intro E _ _ z i h
    exact (T1 E (z ≫ fst _ _) i (memA E z i h)).map _
  · intro E _ _ E' _ _ ψ z i h
    have h' := memA E z i h
    simp only [Category.assoc]
    rw [T2 E E' ψ (z ≫ fst A (epsR R)) i h', epsGen_epsEv_nat]
  · intro E _ _ z i j hi hj
    have hi' := memA E z i hi
    have hj' := memA E z j hj
    have hij : ⊤ ≤ (ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ (P.U i ⊓ P.U j) :=
      fun p hp ↦ ⟨memV E _ i hi' hp, memV E _ j hj' hp⟩
    simp only
    rw [T3 E (z ≫ fst A (epsR R)) i j hi' hj', map_mul, epsGen_key (R := R) (E := E) v z,
      Over.comp_left, spOver_left, evalSectionAtPointOrZero_specMap_comp _ _ E
        (epsEv (R := R) (E := E) (z ≫ snd A (epsR R)) : DualNumber E →+* E) _ _ _ hij]
    rfl

end GlobalTheory.PtExt
