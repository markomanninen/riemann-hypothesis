module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrTbox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSqz

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Fr.pr_tsurj :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → ∀ x ∈ Z1C F.loc (B.bar O).ad (B.bar O).b, ∃ D ∈ Tan O R, ∃ X, ∀ s, B.tanCo O D s = x.1 s + ((B.bar O).ad s X - X) := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hOf hCont hGood x hx
  obtain ⟨hco1, hco2⟩ := co_res O
  haveI := hco1
  haveI := hco2
  have hresk : ∀ c : ResidueField O, res O (ResidueField O) c = c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← IsLocalRing.ResidueField.algebraMap_eq, AlgHom.commutes]
  let p := TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)
  have hresd : ∀ a : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) a = a.fst := by
    intro a
    rw [← res_map p a, hresk]
    rfl
  obtain ⟨-, -, hlc⟩ := pr_open (C₀ := C₀) hF O R B hCont
  obtain ⟨B', hB'c, hB'map, hB'snd⟩ := pr_tbox hF O (B.bar O) hlc x hx
  have hOfbar : (Box.map (p : DualNumber (ResidueField O) →+* ResidueField O) B').Of (ρ.bar O) := by
    rw [hB'map]
    refine ⟨?_, ?_, ?_⟩
    · show ((B.r F.c).mat).map (res O R) = 1
      rw [hOf.atc]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro s
      show ((B.r s).mat).map (res O R) = _
      rw [hOf.res]
      rfl
    · intro v i s
      have e : (((B.bar O).g v : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) * (ρ.bar O).r (F.loc0 v s) *
          ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) =
          (res O R).mapMatrix ((B.g v : Matrix (Fin n) (Fin n) R) * ρ.r (F.loc0 v s) *
            (((B.g v)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) := by
        rw [map_mul, map_mul]
        rfl
      rw [e]
      exact congrArg (res O R) (hOf.psi v i s)
  have hn := pr_norm hF O (DualNumber (ResidueField O)) (ResidueField O) p (ρ.bar O) B'
  have hker : maximalIdeal (DualNumber (ResidueField O)) * RingHom.ker p = ⊥ := by
    refine eq_bot_iff.2 (Ideal.mul_le.2 fun a ha b hb => ?_)
    have ha0 : a.fst = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).1 ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne))
    have hb0 : b.fst = 0 := by simpa [p] using RingHom.mem_ker.1 hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha0, hb0]
  have hbb : NRep.bar O (NRep.bar O ρ) = NRep.bar O ρ := by
    refine NRep.ext ?_ ?_
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      simp only [NRep.bar, NRep.map_r]
      exact hresk _
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      simp only [NRep.bar, NRep.map_ψ]
      exact hresk _
  obtain ⟨h, ρ', hh1, hρ'p, hρ'c, hrc, hr0⟩ := hn hker (by rw [hbb]; exact hGood) hOfbar hB'c
  have hfun : ((res O (DualNumber (ResidueField O))) : DualNumber (ResidueField O) →+* ResidueField O) = (p : DualNumber (ResidueField O) →+* ResidueField O) :=
    RingHom.ext fun a => hresd a
  have hbar' : NRep.bar O ρ' = NRep.bar O ρ := by
    show NRep.map _ ρ' = _
    rw [hfun, hρ'p]
  have hdof : ∃ D ∈ Tan O R, ∀ s, (conjBy h B'.r s).mat.map TrivSqZeroExt.snd = B.tanCo O D s * ((B.bar O).r s).mat := by
    obtain ⟨g, hg, -⟩ := hU.univ _ ρ' hρ'c hbar'
    have hfst : ∀ x, (g x).fst = res O R x := fun x => by
      rw [← hresd (g x), res_map]
    let Dd : R →ₗ[O] ResidueField O :=
      { toFun := fun x => (g x).snd
        map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
        map_smul' := fun a x => by simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
    have hDd : ∀ x, Dd x = (g x).snd := fun _ => rfl
    have hr : (Box.map (g : R →+* DualNumber (ResidueField O)) B).r = conjBy h B'.r := by
      refine pr_ext hF _ _ _ (Box.nu _) (fun s => by simp [conjBy, B'.nu s]) ?_ ?_
      · change (B.r F.c).mat.map g = (conjBy h B'.r F.c).mat
        rw [hOf.atc, hrc]
        exact Matrix.map_one _ (map_zero g) (map_one g)
      · intro s
        change (B.r s).mat.map g = (conjBy h B'.r s).mat
        rw [hOf.res]
        change (ρ.map (g : R →+* DualNumber (ResidueField O))).r s = (conjBy h B'.r s).mat
        rw [hg, hr0]
    refine ⟨Dd, ?_, fun s => ?_⟩
    · intro f hf
      rw [hDd, hDd, hDd, map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
    · rw [← hr]
      show ((B.r s).mat.map g).map TrivSqZeroExt.snd = ((B.r s).mat.map Dd * ((((Box.bar O B).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) * ((((Box.bar O B).r s).left : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
      rw [mul_assoc, Units.inv_mul, mul_one, Matrix.map_map]
      rfl
  obtain ⟨D, hD, hDs⟩ := hdof
  let μ : ResidueField O →+ DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inrHom (ResidueField O) (ResidueField O)).toAddMonoidHom
  have hμ : IsSq O μ := by
    constructor
    · intro a c
      rw [hresd]
      ext
      · simp [μ]
      · simp [μ, TrivSqZeroExt.snd_mul, MulOpposite.smul_eq_mul_unop, smul_eq_mul, mul_comm]
    · intro c
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [μ]
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O (DualNumber (ResidueField O)) n μ hμ
  let Y : Matrix (Fin n) (Fin n) (ResidueField O) := (h : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))).map TrivSqZeroExt.snd
  have hhe : h = e Y := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [he1]
    have h0 := congrFun (congrFun hh1 i) j
    simp only [Matrix.map_apply] at h0
    refine TrivSqZeroExt.ext ?_ ?_
    · by_cases hij : i = j
      · subst hij
        simpa [μ, p] using h0
      · simpa [μ, p, Matrix.one_apply_ne hij] using h0
    · by_cases hij : i = j
      · subst hij
        simp [μ, Y]
      · simp [μ, Y, Matrix.one_apply_ne hij]
  refine ⟨D, hD, -Y, fun s => ?_⟩
  have hgbar : GG.map ((res O (DualNumber (ResidueField O))) : DualNumber (ResidueField O) →+* ResidueField O) (B'.r s) = (B.bar O).r s := by
    rw [hfun, ← hB'map]
    rfl
  have hconj : conjBy h B'.r s = GG.ofGL (e (Y + ((B.bar O).r s).adFun (-Y))) * B'.r s := by
    have h5 := he5 (B'.r s) (-Y)
    rw [hgbar] at h5
    rw [he2, map_mul, mul_assoc, ← h5, ← mul_assoc, ← he3, ← hhe, map_inv]
    rfl
  have hm : ∀ (A : GL (Fin n) (DualNumber (ResidueField O))) (g : GG (m := n) (R := DualNumber (ResidueField O))),
      (GG.ofGL A * g).mat = (A : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))) * g.mat := by
    intro A g
    simp [GG.mat, GG.ofGL]
  have hmat : (conjBy h B'.r s).mat = (B'.r s).mat + ((Y + ((B.bar O).r s).adFun (-Y)) * ((B.bar O).r s).mat).map μ := by
    rw [hconj, hm, he1, add_mul, one_mul, (he4 _ _).2, ← hgbar, GG.map_mat]
    rfl
  have hsnd := hDs s
  rw [hmat] at hsnd
  have hadd : ∀ (P Q : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))),
      (P + Q).map TrivSqZeroExt.snd = P.map TrivSqZeroExt.snd + Q.map TrivSqZeroExt.snd := by
    intro P Q
    ext i j
    simp
  have hmapsnd : ∀ W : Matrix (Fin n) (Fin n) (ResidueField O), (W.map μ).map TrivSqZeroExt.snd = W := by
    intro W
    ext i j
    simp [μ]
  rw [hadd, hmapsnd, hB'snd s, ← add_mul] at hsnd
  have hM : ((B.bar O).r s).mat * (((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O) ) = (1 : Matrix (Fin n) (Fin n) (ResidueField O)) := Units.mul_inv _
  have h6 := congrArg (· * ((((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) hsnd
  simp only [Matrix.mul_assoc, hM, Matrix.mul_one] at h6
  rw [← h6]
  show _ = x.1 s + (((B.bar O).r s).adFun (-Y) - -Y)
  abel
