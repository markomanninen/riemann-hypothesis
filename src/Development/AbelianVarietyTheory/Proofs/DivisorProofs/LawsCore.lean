module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.W0EqOfRtEq
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LawsCore

theorem laws_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) →
    Laws (T.U j) (xiR D) := by
  intro D T hT j hj hF
  have hg : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hLaws : GlobalTheory.LevGeo.Laws D j (T.Q.Xo j) T.Q.c (T.U j) (GlobalTheory.LevGeo.coreDict T.toCore j) := by
    obtain ⟨hH, hL, _, hDat⟩ := hT.pins
    refine ⟨hj, hH, hDat j hj, hL.2, hT.unf j hj, hT.chiTriv j hj, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨th, hr, hinf, hdu⟩ := hT.dictU j hj σ hσ
      obtain ⟨Kf', hr', h1, h2, h3⟩ := GlobalTheory.LevCore.dict_transport (hT.spaceW j hj σ hσ) (T.dict j σ) (GlobalTheory.LevGeo.coreDict T.toCore j σ)
        (fun g h' => by unfold GlobalTheory.LevGeo.coreDict; rw [dite_eq_left h']) (T.Kf j σ) th hr _
        (hL.1 ▸ hT.levelK j hj σ hσ) hdu (hT.muUnit j hj σ hσ).2.2.2
      exact ⟨Kf', th, hr', h1, hinf, h2, h3⟩
    · intro σ hσ
      have h := hT.modelW j hj σ hσ
      rw [hT.spaceW j hj σ hσ] at h
      exact h
  exact (GlobalTheory.LevLaws.laws_of_level D j _ _ _ (T.Q.Xo j) T.Q.c (T.U j) _
    hLaws hF hg).1

end GlobalTheory.LawsCore
