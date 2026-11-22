module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PtHypU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeIIOfBlochKatoLocalPoint
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.KatoTwoW

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase :
    U3.CohInp → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), _root_.UpperTheory.V.Aut.AutBAlt D ι g₁ → _root_.UpperTheory.V.Aut.LemWAlt D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hC hK hRI hRII Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx]
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
    let φ := algebraMap c.O (PadicAlgCl l)
    show (tor c.O (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O).map φ =
      tor (PadicAlgCl l) (Units.map φ.toMonoidHom (D.Ψ g))
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (D.Ψ g) (wt1 i))
  have hCob {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG (m := 3) (R := κ))
      (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) :
      ∃ X, γ = cob r X := by
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp h
    refine ⟨-X, funext fun g => ?_⟩
    show adRep r g X - X = -X - adRep r g (-X)
    rw [map_neg]
    abel
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hC D hM (isPt_push D hM S f hf) hU hL
  · have hLoc : IsLocPt (toBar x₀) := by
      intro y hy
      have hsurj : Function.Surjective x₀ := fun a => ⟨algebraMap c.O S.R a, x₀.commutes a⟩
      have hmax : (Ideal.comap (x₀ : S.R →+* c.O) (IsLocalRing.maximalIdeal c.O)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ hsurj
      have hxy : x₀ y ∈ IsLocalRing.maximalIdeal c.O := by
        change y ∈ Ideal.comap (x₀ : S.R →+* c.O) (IsLocalRing.maximalIdeal c.O)
        rwa [IsLocalRing.eq_maximalIdeal hmax]
      have hnonunit := (IsLocalRing.mem_maximalIdeal _).mp hxy
      change ‖(x₀ y : PadicAlgCl l)‖ < 1
      by_cases hzero : x₀ y = 0
      · simp [hzero]
      have hval : (IsDiscreteValuationRing.addVal c.O (x₀ y)).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
          IsDiscreteValuationRing.addVal_eq_top_iff]
        exact fun h => h.elim hnonunit hzero
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      have hpow := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hval
      rw [← normO l c.O (x₀ y) hzero] at hpow
      exact lt_of_not_ge fun h => (not_lt_of_ge (one_le_pow₀ h)) hpow
    have h1 := tanCoc_isBK hC D hM S F (hF ▸ hLoc)
    rw [hF, h0] at h1
    rw [h0]
    exact hCob _ _ (bloch_kato_nonpositive_weight hC D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hC D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hPush : IsPush (f.comp (entAlg c.O S.r.hom).val) S.r.hom (push f S.r.hom) := by
      intro g
      refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
      unfold entAlg
      exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hRI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult hPush h)
      · exact _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext hC hK hRII D hM S f hf.1 ι h
          (hW U S _ _ hPush h (typeII_facts hC D hM hp h).1)
    exact hCob _ _ (hz _ h1.1 h1.2)
end
