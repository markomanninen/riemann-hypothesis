module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerFree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_free : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hO La _ _ _ L _ _ X _ _ G e τ hre
  have counit_eq (n : ℕ) (a : G.A n) :
      Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
    have h := hre.pt 0 n a
    rw [map_zero] at h
    exact h
  have mem_sq_iff (n : ℕ) (a : G.A n) :
      a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔
        e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
    have hker : (BT.augIdeal (X.A n)).comap (e n) =
        RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
      ext b
      rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq]
    have hmap : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) =
        BT.augIdeal (X.A n) := by
      rw [← hker, Ideal.map_comap_of_surjective _ (e n).surjective]
    rw [← hmap, ← Ideal.map_pow]
    constructor
    · exact Ideal.mem_map_of_mem _
    · intro h
      obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h
      rwa [← (e n).injective hab]
  have dUnit_eq_zero_iff (n : ℕ) (a : G.A n) :
      PDiv.dUnit (R := O) a = 0 ↔ X.der n (e n a).1 0 := by
    rw [PDiv.dUnit, AugCot.d_eq_zero_iff, mem_sq_iff, map_sub, AlgEquiv.commutes]
    set c := Bialgebra.counitAlgHom O (G.A n) a with hc
    have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
    constructor
    · intro h
      have hd := PositivityTheory.HtPt.Twomega.der_of_mem_sq X n _ h
      simpa using X.der_add n _ _ _ _ hd hc'
    · intro h
      have hd := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ h hc'
      rw [sub_zero] at hd
      refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ hd
      rw [OrderApi.mem_augIdeal, hc, counit_eq]
      exact sub_self _
  have dUnit_eq_iff (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
      (h : X.der n (e n a).1 w) : PDiv.dUnit (R := O) b = PDiv.dUnit (R := O) a ↔ X.der n (e n b).1 w := by
    rw [← sub_eq_zero, PDiv.dUnit, PDiv.dUnit, ← map_sub]
    refine (dUnit_eq_zero_iff n (b - a)).trans ?_
    rw [map_sub]
    constructor
    · intro hd
      simpa using X.der_add n _ _ _ _ hd h
    · intro hd
      have hsub := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ hd h
      rwa [sub_self] at hsub
  have exists_der (n : ℕ) (w : Module.Dual O L) : ∃ a : G.A n, X.der n (e n a).1 w := by
    obtain ⟨f, hf, h⟩ := X.der_onto n w
    exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩
  let cls (n : ℕ) (w : Module.Dual O L) := PDiv.dUnit (R := O) (exists_der n w).choose
  have dUnit_eq_cls (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
      PDiv.dUnit (R := O) a = cls n w ↔ X.der n (e n a).1 w :=
    dUnit_eq_iff n _ a w (exists_der n w).choose_spec
  have der_res (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
      (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
    X.der_res n _ _ w h (hre.res n a)
  let toOmega : Module.Dual O L →ₗ[O] G.omega :=
    { toFun := fun w => ⟨fun n => cls n w, fun n => by
        obtain ⟨a, ha⟩ := exists_der (n + 1) w
        change PDiv.cotMap (G.res n) (cls (n + 1) w) = cls n w
        rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.cotMap_d, dUnit_eq_cls]
        exact der_res n a w ha⟩
      map_add' := fun w w' => Subtype.ext (funext fun n => by
        obtain ⟨a, ha⟩ := exists_der n w
        obtain ⟨b, hb⟩ := exists_der n w'
        change cls n (w + w') = cls n w + cls n w'
        rw [← (dUnit_eq_cls _ a w).2 ha, ← (dUnit_eq_cls _ b w').2 hb,
          PDiv.dUnit, PDiv.dUnit, ← map_add (f := _), eq_comm]
        refine (dUnit_eq_cls _ _ _).2 ?_
        rw [map_add (f := _)]
        exact X.der_add n _ _ _ _ ha hb)
      map_smul' := fun r w => Subtype.ext (funext fun n => by
        obtain ⟨a, ha⟩ := exists_der n w
        change cls n (r • w) = r • cls n w
        rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.dUnit, ← map_smul, eq_comm]
        refine (dUnit_eq_cls _ _ _).2 ?_
        rw [map_smul]
        exact PositivityTheory.HtPt.Twomega.der_smul X n r _ _ ha) }
  have toOmega_val (w : Module.Dual O L) (n : ℕ) : (toOmega w).1 n = cls n w := rfl
  have toOmega_bijective : Function.Bijective toOmega := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      refine PositivityTheory.HtPt.Twomega.eq_zero_of_cong hO w fun n => ?_
      have h0 : PDiv.dUnit (R := O) (0 : G.A n) = 0 := map_zero _
      have h1 : cls n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
      exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff n 0).1 h0)).1
        ((dUnit_eq_cls n 0 w).1 (h0.trans h1.symm))
    · intro ω
      choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
      choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
      obtain ⟨W, hW⟩ := PositivityTheory.HtPt.Twomega.exists_lim hO w fun n => by
        refine (X.der_unique n _ _ _ (hw n)).1 ?_
        refine (dUnit_eq_iff n _ _ _ (der_res n _ _ (hw (n + 1)))).1 ?_
        rw [← PDiv.cotMap_d, PDiv.dUnit, PDiv.dUnit, ha, ha]
        exact (ω.2 n).symm
      refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
      rw [toOmega_val, ← ha, eq_comm]
      exact (dUnit_eq_cls n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))
  let k := LinearEquiv.ofBijective toOmega toOmega_bijective
  have hk (ω : G.omega) (n : ℕ) : ω.1 n = cls n (k.symm ω) :=
    congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
  refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
  · exact (dUnit_eq_cls n _ _).1 (hk (dlog G χ) n)
  · rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun n => ?_)
    obtain ⟨a, ha⟩ := exists_der n (k.symm ω)
    rw [omegaMap_val, hk ω n, ← (dUnit_eq_cls n a _).2 ha, PDiv.cotMap_d]
    exact (dUnit_eq_cls n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)
