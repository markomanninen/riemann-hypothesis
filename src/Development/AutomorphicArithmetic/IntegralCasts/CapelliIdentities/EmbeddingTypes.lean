module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.Reformulated.B.EmbeddingTypes.core {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ s ∈ nonZeroDivisors R, s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ y hy
  exact ⟨t, t.2, by simpa [Submonoid.smul_def] using ht⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt :
    ∀ (D : Formalism.BasicNotions.D7) (j : ℕ) (y : (D.sp.W j).V),
    ∃ s ∈ nonZeroDivisors (NumberField.RingOfIntegers D.host.E),
      s • y ∈
        (D.sp.W
            j).L0 := by
  intro D j y
  classical
  let S := D.sp.W j
  have hspan : Submodule.span D.host.E (S.L0 : Set S.V) = ⊤ := by
    let W := Submodule.span D.host.E (S.L0 : Set S.V)
    change W = ⊤
    by_contra h
    let b := Module.finBasis D.host.E W
    let g : S.V →ₗ[D.host.E] (Fin (Module.finrank D.host.E W) → D.host.E) :=
      LinearMap.pi fun k => S.hT (b k)
    have hdim : Module.finrank D.host.E (Fin (Module.finrank D.host.E W) → D.host.E) < Module.finrank D.host.E S.V := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hzero (y : W) : S.hT y x = 0 := by
      have hb : ∀ k, S.hT (b k) x = 0 := by
        intro k
        exact congrFun (LinearMap.mem_ker.mp hx) k
      have hy : y ∈ Submodule.span D.host.E (Set.range b) := b.span_eq ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem z hz => obtain ⟨k, rfl⟩ := hz; exact hb k
      | zero => simp
      | add u v _ _ hu hv => simp [map_add, hu, hv]
      | smul a z _ hz => simp [LinearMap.map_smulₛₗ, hz]
    have hsmul (a : D.host.E) : a • x ∈ S.L0 := by
      rw [← S.baseLattice_isUnimodular]
      change a • x ∈ Formalism.E.hdual S.hT S.L0
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      have hyzero := hzero ⟨y, Submodule.subset_span hy⟩
      simp [map_smul, hyzero]
    let i : D.host.E →ₗ[NumberField.RingOfIntegers D.host.E] S.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ x).restrictScalars _).codRestrict S.L0 hsmul
    let : Module.Finite (NumberField.RingOfIntegers D.host.E) S.L0 :=
      Module.Finite.iff_fg.mpr S.standardTuple_isLattice.fg
    let : Module.Finite (NumberField.RingOfIntegers D.host.E) D.host.E :=
      Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E hx₀ (congrArg Subtype.val hab)
    exact NumberField.RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (NumberField.RingOfIntegers D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact UpperTheory.Reformulated.B.EmbeddingTypes.core (K := D.host.E) _ hspan y
