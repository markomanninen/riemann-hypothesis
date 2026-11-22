module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdmissibleRankTwoSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.KillsComp
end GlobalTheory.KillsComp
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2.IrrTransfer
end GlobalTheory.Ord2.IrrTransfer
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2
open UpperTheory.V.Base UpperTheory.V.U3 in
theorem admissible_typeII_block_alt : U3.CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* U3.GG (m := 3) (R := PadicAlgCl l)} (_ : D.IsPt U g₁ r) (ι : Qbar l ≃+* ℂ), U3.TypeII D.η r → ∀ W : R2 Ω l, D.IsExt r W → Continuous W → (∀ g, (mat W g).det = ((D.η g : ℤˣ) : ℤ)) → D.IsModularDense ι W → admitted ι e W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII W hext hcont hdet hmod
  have hdt : ∀ g, (dt W g : Qbar l) = ((D.η g : ℤˣ) : ℤ) := fun g => hdet g
  obtain ⟨A, hA, -, hIA, -, -, -, -⟩ := dat_loc D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hA
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  let χ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω (HV.comp l ψ))
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hχ2 : ∀ g, χ g * χ g = 1 := fun g => by
    have h1 : Chr.dirG ℚ Ω (HV.comp l ψ) g * Chr.dirG ℚ Ω (HV.comp l ψ) g = 1 := by
      apply Units.ext
      show (HV.comp l ψ) (Chr.cls ℚ Ω N g) * (HV.comp l ψ) (Chr.cls ℚ Ω N g) = 1
      rw [← MulChar.mul_apply, ← sq, D.gd.ine, MulChar.one_apply (Units.isUnit _)]
    show Units.map _ _ * Units.map _ _ = 1
    rw [← map_mul, h1, map_one]
  have hψχ : ∀ s ∈ Ine (F := ℚ) A, ψQ s = χ s := fun s hs => by
    rw [← hIA] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    show Units.map _ _ = Units.map _ _
    rw [psi_ine D g hg]
  have hlocal : ∃ κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ,
      Af.IsFlagOn W (Dec (F := ℚ) A) κ ∧
        ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
          κ 0 s = D.ΨQ s ∧ κ 1 s = (D.ΨQ s)⁻¹ := by
    have h11 := (typeII_facts hC D hM h hII).1
    have hblk (s : G ℚ Ω) (hs : s ∈ D.η.ker) :
        (r s).mat = !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] := by
      have hcorner := hext.1 s hs
      have e01 := hII.1 s hs 0 1 (by decide)
      have e10 := hII.1 s hs 1 0 (by decide)
      have e12 := hII.1 s hs 1 2 (by decide)
      have e21 := hII.1 s hs 2 1 (by decide)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [show mat W s = corner (r s).mat from hcorner, corner, e01, e10, e12, e21, h11 s hs]
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hA
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hA
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l :=
      ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := by
      intro s hs
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      have hconj : (conjBy M r s).mat =
          (M : Matrix (Fin 3) (Fin 3) (Qbar l)) * (r s).mat *
            ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) := by
        simp [conjBy, GG.mat, hr]
      have hcol : (conjBy M r s).mat *ᵥ Pi.single 0 1 =
          (D.ΨQ s : Qbar l) • (Pi.single 0 1 : Fin 3 → Qbar l) := by
        rw [Matrix.mulVec_single_one]
        funext i
        simp only [Matrix.col_apply]
        fin_cases i
        · simpa [GG.mat, tor_val, wt1] using hdiag s hs 0
        · simpa using hup s (hID hs) (hIk hs) 1 0 (by decide)
        · simpa using hup s (hID hs) (hIk hs) 2 0 (by decide)
      rw [← hblk s (hIk hs), hv, ← Matrix.mulVec_smul, ← hcol, hconj,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul]
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    exact UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
  obtain ⟨κ, hflag, hκ⟩ := hlocal
  refine ⟨hcont, ?_, fun s hs => Units.ext ?_, GlobalTheory.Ord2.irr_transfer D.η D.η_ker W hdet (typeII_irr_cyc hC D hM h hII W hext),
    ?_, ?_, A, χ, κ, ?_, fun s hs => ?_, hflag, fun s hs => ?_, fun s hs => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [MonoidHom.one_apply, Units.val_one, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hdt]
    rcases Int.units_eq_one_or (D.η g) with h1 | h1 <;> simp [h1]
  · rw [hdt, conj_eta D s hs]
    simp
  · have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
    exact ⟨_, Nat.mul_pos (NeZero.pos N) hodd.pos, (typeII_ord hC D hM h hII W hext hcont hdet).1.away⟩
  · obtain ⟨f, hf⟩ := _root_.UpperTheory.GalN.V.mod0'_alt hmod
    refine ⟨f, 1, 1, le_rfl, fun _ _ => rfl, ?_⟩
    rw [mul_one]
    exact hf
  · obtain ⟨h1, h2, h3, -⟩ := places ℚ Ω l A
    have hne : A ≠ ⊤ := fun ht => (h2 ht).2 hA
    obtain ⟨v, hv⟩ := h1 hne
    exact ⟨v, hv, (h3 v hv).1 hA⟩
  · show Units.map _ _ = 1
    rw [GlobalTheory.killsMu_comp_of_sq_eq_one ψ D.gd.l_odd D.gd.ine s hs, map_one]
  · rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hdt, hIk hs]
    simp
  · rw [(hκ s hs).1, (hκ s hs).2, hΨ, hψχ s hs, mul_inv, ← zpow_neg]
    refine ⟨rfl, ?_⟩
    congr 1
    exact inv_eq_of_mul_eq_one_right (hχ2 s)
end GlobalTheory.Ord2
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2
open TwDet
end GlobalTheory.Ord2
end
end
