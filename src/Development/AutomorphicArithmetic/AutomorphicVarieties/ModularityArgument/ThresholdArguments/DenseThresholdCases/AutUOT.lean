module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Link2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobLG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
private theorem part2 (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {ι : Qbar l ≃+* ℂ}
    {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) (hi : Af.IsIrr (ρ.comp V.pr)) :
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  have hc : Continuous (ρ.comp V.pr) := hρ.comp (V.pr_cont W.continuous_resP)
  have hoff : ∀ᶠ w : Plc L in Filter.cofinite, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.mp hw)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.link2_alt H L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ _ hc hi
    (hoff.mono fun w hw hsp τ hτ B hB => _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hw hB (hLG w hsp τ hτ))
theorem autUO_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Ord.AutUOAlt := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin m) f) := by
      intro A B hAB
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact hf (congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB)
    rw [← MonoidHom.ker_comp_of_injective τ₀ _ hmap]
    exact (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, -, hcomp, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt H l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧
    GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)} => Y.1.Y) ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, -, p5⟩ := part2 H s hn Y.cont σ.2 hLG hi
  refine ⟨π, p1, p2, p3, fun v => ?_⟩
  have hsplit : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
      (HeightOneSpectrum.ext (Ideal.ext fun x =>
        (show _ ↔ _ from (s.hw v.1) (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v.1 x)))
  exact (p5 _ hsplit _).2 (hcomp v)
end UpperTheory.Gal.projectedFormsSystemPart
end
