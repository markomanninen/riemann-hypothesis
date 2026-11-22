module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartLinkAltAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicTensorInductionOfLocalPlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRec

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
theorem UpperTheory.Gal.projectedFormsSystemPart.autAway_alt (PH : _root_.UpperTheory.V.Af.HypothesesH') (hL : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L]
    [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) (V : s.Lev)
    (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hτ : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (hS : V.S' = s.S) :
    (hset Q τ₀).AutomorphicHeckeSet ι fun _ ρ => Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : IsAdicComplete (maximalIdeal c.O) c.O := hc
    have : Finite (ResidueField c.O) := hfin
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let j : ResidueField c.O →+* Perfection (c.O ⧸ maximalIdeal c.O) l :=
      Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
        (RingHom.id (ResidueField c.O))
    let τ : ResidueField c.O →* c.O := (Perfection.teichmuller l (maximalIdeal c.O)).comp j
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x := by
      have hj := (Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)).symm_apply_apply
        (RingHom.id (ResidueField c.O))
      exact (Perfection.mk_teichmuller (j x)).trans (RingHom.congr_fun hj x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hker : ((Matrix.GeneralLinearGroup.map f).comp τ₀).ker = τ₀.ker := by
      refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
    exact hker ▸ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, hP⟩ := hL l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → AwayOk s ι (Y.r.comp V.pr)} => Y.1.Y)
    ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := hP hi
  refine ⟨π, p1, p2, p3, fun w hw hw0 => ?_⟩
  by_cases hwS : w.under (𝓞 (Lp L)) ∈ V.S'
  swap
  · obtain ⟨B, hB⟩ := p4 w (partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 w hwS)
    exact ImaginaryQuadraticEtaCharacter.sphUnl L n hn π w B hB
  obtain ⟨hwv, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  rw [hS] at hwS
  have hu : w.under (𝓞 (Lp L)) ∈ s.St := by
    rcases hwS with h | h | h
    · refine absurd ?_ hw
      rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
      exact h
    · exact h
    · exact absurd h hw0
  refine hC L n hn π p2 (s.w (w.under (𝓞 (Lp L)))) w (hwv _).symm ?_
  refine (ImaginaryQuadraticEtaCharacter.plainIff L n hn π _).1 fun τ hτ' => ?_
  classical
  have hs : ∀ u : s.St, IsSplitAt (s.w u) := fun u => hsp _ (by
    rw [hwv]
    exact s.split _ (Or.inr (Or.inl u.2)))
  choose loc hloc using fun u : s.St => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PH.toClassicalTheorems L n π (s.w u)).1
  obtain ⟨rc, hrc⟩ := PH.toClassicalTheorems.exists_reciprocity_dense (s.hw (w.under (𝓞 (Lp L))))
  have k := _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 _ (hτ t ht)
    (Function.update loc ⟨_, hu⟩ τ) (fun u' => p5 _ (hs u') _ (by
      by_cases e : u' = ⟨_, hu⟩
      · subst e
        rwa [Function.update_self]
      · rw [Function.update_of_ne e]
        exact hloc _)) ⟨_, hu⟩ rc hrc
  rw [Function.update_self] at k
  exact typePlain L Ω n hn π _ _ (s.hw _) τ hτ' rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT PH.toClassicalTheorems hrc)
    (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) k
end
