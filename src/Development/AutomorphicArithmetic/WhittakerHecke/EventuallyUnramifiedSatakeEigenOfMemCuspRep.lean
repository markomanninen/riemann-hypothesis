module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.eventually_unramified_satake_eigen_of_mem_cuspRep :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (f : Sm E 2), f ∈ P.V → ∀ h : GL (Fin 2) (A E), ∀ᶠ v : H.P ℚ in cofinite, H.Gd D.δ v ∧ ∀ w : H.P E, w.under (𝓞 ℚ) = v → Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h)) := by
  intro E _ _ _ D P f hf h
  have hδ : D.δ ≠ 0 := (by
    intro e
    have := D.neg (algebraMap ℚ ℝ)
    rw [e, map_zero] at this
    exact lt_irrefl _ this)
  have hF : ∀ᶠ w : H.P E in cofinite, H.Fix w f.1 :=
    (H.aeK E).2.2 f.1 (by
      have hO : {k : GL (Fin 2) (Af E) | ∀ g, f.1 (g * finGL E 2 k) = f.1 g} = {k | finRep E 2 k f = f} :=
        Set.ext fun k => ⟨fun hk => Subtype.ext (funext hk), fun hk g => congrFun (congrArg Subtype.val hk) g⟩
      rw [hO]
      exact (P.cusp f hf).1.level)
  have hall : ∀ᶠ w : H.P E in cofinite, Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h)) := by
    have hint : ∀ᶠ w : H.P E in cofinite, H.cp w (rt D.θ) ∈ w.adicCompletionIntegers E := (rt D.θ).2.2
    filter_upwards [hint, hF, (H.aeK E).1 h, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat P] with w h1 h2 h3 ⟨B, hB⟩
    have hE : EigAt w B f.1 := by
      have hSat := (CG.hasSat_mk P w B).1 hB
      intro g
      refine ⟨hSat.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
      · rw [map_mul, map_mul, ← mul_assoc]
        exact h2 _ k hk
      · by_cases h0 : f = 0
        · subst h0
          simp
        have he := (hSat.2 (⟨f, hf⟩ : P.V)
          (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun x => h2 x k hk)))
          fun h => h0 (congrArg Subtype.val h)).2.2.2 ϖ hϖ j hj
        let ev : P.V →+ ℂ :=
          { toFun := fun ψ => ψ.1.1 (g * finGL E 2 (locGL E 2 w y))
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2)
          (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (P.locRep w) ⟨f, hf⟩)
        refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
        rw [map_mul, map_mul, ← mul_assoc]
        rfl
    have ht := H.fixTr E w f.1 h h3
    exact ⟨h1, ht.1 h2, B, hB, ht.2 B hE⟩
  have hfin := (Set.Finite.image (fun w : H.P E => w.under (𝓞 ℚ)) (show Set.Finite _ from hall)).compl_mem_cofinite
  filter_upwards [H.gdAe ℚ D.δ hδ, hfin] with v hv hn
  refine ⟨hv, fun w hw => ?_⟩
  by_contra hc
  exact hn ⟨w, hc, hw⟩
