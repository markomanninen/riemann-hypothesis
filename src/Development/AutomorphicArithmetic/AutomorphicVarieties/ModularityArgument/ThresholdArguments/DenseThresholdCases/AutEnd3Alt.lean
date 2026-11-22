module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Loc2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V UpperTheory.V.Z.Win
theorem UpperTheory.V.Z.Win.Dn.autEnd3_alt :
    _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → Sd.IsCC σ → ∀ (ι : Qbar l ≃+* ℂ),
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], (∀ [Algebra K Ω], Base.galOf ℚ K Ω = η.ker) →
    (∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A)), OrdPt l η Ψ σ g₁ B r →
      (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) →
      ∀ [Algebra K Ω] [Algebra K L] [IsScalarTower K L Ω] (ρ : G K Ω →* GL (Fin 3) (Qbar l)),
        (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)).mat) → IneAb ρ ∧ Flagged ρ ∧ Keeps ρ L) → _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι (cycBar L Ω l)⁻¹ → _root_.UpperTheory.V.Pr.AutEnd3Alt c η Ψ σ g₁ B K ι := by
  intro hD Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ Φ k _ C₀ hok hl hcc ι K _ _ _ hK hS hA A dvrA _ r hr hirr _ ρ hρ
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI : IsGalois L Ω := {}
  have hσ : σ * σ = 1 := by
    obtain ⟨j, hj⟩ := hcc
    exact AlgEquiv.ext fun x => j.injective (by simp [AlgEquiv.mul_apply, hj])
  have hησ : η σ = -1 := by
    obtain ⟨hc, ec⟩ := k.c
    have h := k.del ⟨σ, hc⟩
    rw [ec, hok.del_c] at h
    exact h.symm
  have hLη : Base.galOf ℚ L Ω ≤ η.ker := k.gal ▸ inf_le_right
  have hKL : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun f =>
      (hK.ge (hLη (Base.galEmb_mem ℚ L Ω f))) x
  choose f hf using hKL
  have hinj := (algebraMap L Ω).injective
  let φ : K →+* L :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  letI : Algebra K L := φ.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  haveI := k.ab
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have : IsLocalRing A := dvrA.toIsLocalRing
  obtain ⟨_, hloc, hcont⟩ := UpperTheory.V.Th.End3.sub_facts c A
  have : IsLocalHom (algebraMap c.O A) := hloc
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  obtain ⟨ρ', h1, h2, h3⟩ := exists_nrep3 k hok hl hσ r hr
  have hU := hirr (Base.galOf ℚ L Ω) (Base.galEmbTop ℚ L Ω).2.1 hLη
  have hcomp : ∀ s : G L Ω, Base.galEmb ℚ K Ω (Base.galEmb K L Ω s) = Base.galEmb ℚ L Ω s := fun s => rfl
  have hρL (s : G L Ω) : (ρ (Base.galEmb K L Ω s)).val =
      (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ L Ω s)).mat := by
    rw [hρ, hcomp]
  have irreducible {Γ : Type} [Group Γ] (τ : Γ →* GL (Fin 3) (Qbar l))
      (hτ : ∀ g ∈ Base.galOf ℚ L Ω, ∃ s, ∃ t : Qbar l,
        (UnitaryThreeInertia.push A.val r g).mat = t • (τ s).val) : Af.IsIrr τ := by
    refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hi => hU W fun g hg v hv => ?_⟩
    obtain ⟨s, t, e⟩ := hτ g hg
    change (UnitaryThreeInertia.push A.val r g).mat.mulVec v ∈ W
    rw [e, Matrix.smul_mulVec]
    exact W.smul_mem t (hi s v hv)
  have haut := hA A ρ' h1 (by
    intro v i g hg
    rw [h3 v i g hg, UnitaryThreeInertia.psi]
    have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl
    rw [h6]) (ρ.comp (Base.galEmb K L Ω)) (by
    intro s
    rw [h2]
    exact hρL s) (irreducible _ (by
    intro g hg
    obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
    refine ⟨s, 1, ?_⟩
    change _ = (1 : Qbar l) • (ρ (Base.galEmb K L Ω s)).val
    rw [one_smul]
    exact (hρL s).symm))
  have hEntry : Continuous fun g : G ℚ Ω => (r g).mat.map (A.val : A →+* PadicAlgCl l) := by
    refine continuous_matrix fun a b => hcont _ (fun g => (r g).mat a b) fun n => ?_
    exact (hr.cont n).comp fun X => X a b
  have hχ : Continuous fun s : G K Ω => (cycBar K Ω l s)⁻¹ :=
    (UpperTheory.V.Th.End3.cyc_cont K Ω l).inv
  obtain ⟨s1, s2, s3⟩ := hS A r hr hirr ρ hρ
  have f1 := (flagLaws K Ω l 3 ρ).2.1 (cycBar K Ω l)⁻¹
  have f2 := (flagLaws L Ω l 3 (ρ.comp (Base.galEmb K L Ω))).2.1 (cycBar L Ω l)⁻¹
  refine hD K L Ω l ι 3 (by norm_num) (Af.tw ρ (cycBar K Ω l)⁻¹) σ hcc ?_
    ⟨Jgl (R := Qbar l) 3, fun s s' hs => ?_⟩ ?_ (f1.1 hχ s1) (f1.2.1 s2)
    (fun w hw hu => (f2.2.2 w).1.1 (s3 w hw ((f1.2.2 _).1.2 hu))) haut
  · refine _root_.UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom _ ?_
    simp only [Af.tw_val, hρ]
    exact (Units.continuous_val.comp hχ).smul
      (hEntry.comp (Base.galEmbTop ℚ K Ω).1.continuous)
  · have pairing {x y j : GG (m := 3) (R := PadicAlgCl l)} (hj : j.mat = 1) (hj' : j.right = -1)
        (h : y * j = j * x) : x.mat.transpose * Jmat _ 3 * y.mat = Jmat _ 3 := by
      have h1 : j.left = 1 := Units.ext hj
      have h2 := congrArg SemidirectProduct.left h
      simp only [SemidirectProduct.mul_left, h1, hj', map_one, mul_one, one_mul, sgnAct_neg_one] at h2
      rw [GG.mat, GG.mat, h2, theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ (Jmat _ 3) (Jmat _ 3), Jmat_mul_Jmat, Matrix.mul_one,
        ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
      simp
    have hp := pairing (x := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)) (y := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s'))
      (j := UnitaryThreeInertia.push A.val r σ)
      (by
        show (r σ).mat.map _ = 1
        rw [hr.norm.atc]; simp)
      ((hr.red.mult σ).trans hησ)
      (by rw [← map_mul, ← map_mul, hs, inv_mul_cancel_right])
    have he : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (Base.galEmb ℚ K Ω s') = cycBar ℚ Ω l (Base.galEmb ℚ K Ω s)
      rw [hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [Af.tw_val, Af.tw_val, hρ, hρ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    show _ • (_ * Jmat _ 3 * _) = _ • Jmat _ 3
    rw [hp, MonoidHom.inv_apply, MonoidHom.inv_apply, he, MonoidHom.zpow_apply, ← Units.val_mul]
    congr 2
    rw [show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, zpow_add, zpow_neg_one]
  · refine irreducible _ fun g hg => ?_
    obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
    refine ⟨s, (cycBar K Ω l (Base.galEmb K L Ω s) : Qbar l), ?_⟩
    change _ = (cycBar K Ω l (Base.galEmb K L Ω s) : Qbar l) •
      (Af.tw ρ (cycBar K Ω l)⁻¹ (Base.galEmb K L Ω s)).val
    rw [Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.mul_inv, one_smul]
    exact (hρL s).symm
end
