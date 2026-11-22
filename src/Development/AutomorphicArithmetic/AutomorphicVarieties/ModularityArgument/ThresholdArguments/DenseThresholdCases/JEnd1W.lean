module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeIdealEnd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
open UpperTheory.GalN.V
theorem UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 L),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
    intro w
    have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L
      (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
        obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
        ext x
        apply (algebraMap L Ω).injective
        exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
    have hbot : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
    have he := UpperTheory.V.CF.ineCard.1 (Lp L) L w
    rw [hbot, Subgroup.card_bot] at he
    exact Ideal.ramificationIdx_eq_one_iff.1 he.symm
  refine fun x h hx ha => ?_
  · obtain ⟨lam, ρ, hc, hs, hP, hr⟩ := _root_.hecke_ideal_end H hn hJ x h hx ha
    have hc' : Continuous (ρ.comp V.pr) := hc.comp (V.pr_cont W.continuous_resP)
    have hs' : Formalism.MainNotions.N.IsSSRep (ρ.comp V.pr) := by
      intro M hM
      obtain ⟨M', hM', hcompl⟩ := hs M (fun g => by
        obtain ⟨g', rfl⟩ := hpr g
        exact hM g')
      exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
    obtain ⟨σ, hσ, hlg, -⟩ := hP.aut
    exact ⟨_, hc', hs', hr,
      _root_.UpperTheory.V.Z.Win.Gu.endShape'_alt H L Ω hunr l s.odd ι n hn σ hσ _ hc' hs' hlg⟩
end
