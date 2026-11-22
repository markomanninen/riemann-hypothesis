module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Rwwd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Monosep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.rw_of_ordForm (PH : HypothesesH) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  have P := PH.toClassicalTheorems
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  refine hG.ratio w hl A h rc hrc σ hσ ?_
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    let τ := π.locRep w
    let R := MonoidAlgebra ℂ (GL (Fin 2) (w.adicCompletion F))
    have : IsSimpleModule R σ.ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule σ.ρ).1 σ.irred
    have htop : isotypicComponent R τ.asModule σ.ρ.asModule = ⊤ := by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ _) := trivial
      rw [← (hiso σ hσ).2] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨x, rfl⟩
        let x' : σ.ρ.asModule := σ.ρ.asModuleEquiv.symm x
        let f' := Representation.IntertwiningMap.equivLinearMapAsModule σ.ρ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        change f' x' ∈ _
        rcases f'.injective_or_eq_zero with h | h
        · have hrange : LinearMap.range f' ≤ isotypicComponent R τ.asModule σ.ρ.asModule :=
            le_sSup ⟨(LinearEquiv.ofInjective f' h).symm⟩
          exact hrange ⟨x', rfl⟩
        · rw [h, LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · rw [τ.asModuleEquiv.symm.map_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        rw [τ.asModuleEquiv.symm.map_add]
        exact add_mem hx hy
    have : IsSemisimpleModule R τ.asModule :=
      IsSemisimpleModule.congr (M := isotypicComponent R τ.asModule σ.ρ.asModule)
        (LinearEquiv.ofTop _ htop).symm
    have hTv : ∃ T : τ.asModule →ₗ[R] σ.ρ.asModule, T v ≠ 0 := by
      obtain ⟨m, hm, hvm⟩ : ∃ m : Submodule R τ.asModule, IsCoatom m ∧ v ∉ m := by
        by_contra hn
        push Not at hn
        refine hv ((Submodule.mem_bot (M := τ.asModule) R).1 ?_)
        rw [← IsSemisimpleModule.jacobson_eq_bot R τ.asModule]
        exact Submodule.mem_sInf.2 hn
      obtain ⟨W, hW⟩ := exists_isCompl m
      have : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hW.isCoatom_iff_isAtom.1 hm)
      obtain ⟨e⟩ := IsIsotypicOfType.of_isotypicComponent_eq_top htop W
      refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hW.symm, fun he => hvm ?_⟩
      apply (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).1
      apply e.injective
      rw [e.map_zero]
      exact he
    obtain ⟨T, hTv⟩ := hTv
    let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ.ρ).symm T
    obtain ⟨B, hB⟩ := (satLoc P F 2 w σ).1 ⟨T' v, hTv, fun u hu => by
      have hmem : u ∈ K1 w 0 := by
        obtain ⟨k, rfl⟩ := hu
        refine ⟨k, ?_, rfl⟩
        have : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
          Ideal.Quotient.subsingleton_iff.2 (by simp)
        exact Subsingleton.elim (α := Fin 2 → _) _ _
      exact (LinearMap.congr_fun (T'.2 u) v).symm.trans (congrArg T' (hf u hmem))⟩
    exact WD.unr_mono0 _ (UpperTheory.GalN.V.unr_algNorm hrc σ B hB)
  · have hA : ¬ A.valuation (l : Ω) < 1 := fun e => hl (((UpperTheory.V.Base.places F Ω l A).2.2.1 w h).1 e)
    obtain ⟨s₀, hs₀, h0⟩ := IsConcreteLE.not_le_iff_exists.1 fun e => ((H.ram w A h).1 e).elim hc hl
    obtain ⟨g, hg⟩ := UpperTheory.V.Sd.ordAway_n PH F Ω l ι ξ s c m a π r H A hA
    refine UpperTheory.GalN.V.L.monosep F Ω A w h _ (ineIncl h ⟨s₀, hs₀⟩) (deg_ineIncl _) ?_
    have k : UpperTheory.GalN.V.WDN ι r (rc (algNorm σ)) :=
      .of_aw hl H.cont ⟨(hG.away w hl A h rc hrc σ hσ).pol, (hG.away w hl A h rc hrc σ hσ).n0⟩
    have e : (r s₀ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C 1) * (X - C (ξ s₀ : Qbar l)) := by
      rw [← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, hg s₀ hs₀,
        Matrix.charpoly_diagonal, Fin.prod_univ_two]
      rfl
    rw [WD.eig, ← k.charpoly hl, coe_ineIncl, e]
    have h1 : ι (ξ s₀ : Qbar l) ≠ 1 := fun e' => h0 (Units.ext (ι.injective (by simpa using e')))
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, map_X, map_C, map_C]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
    simpa using h1.symm
