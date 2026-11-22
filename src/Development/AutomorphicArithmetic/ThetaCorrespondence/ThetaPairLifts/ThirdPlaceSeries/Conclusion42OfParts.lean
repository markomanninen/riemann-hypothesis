module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGalois
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeights
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsDeRham
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChangeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MuBlockMemStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.NRows.Parts
theorem conclusion42_of_parts (D : D7) (a : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D) (s : GlobalTheory.RowCopy.RowSize D) (hk : GlobalTheory.RowCopy.HeckeSplitOne D)
    (l : ∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) (th : GlobalTheory.RowCopy.ThetaOne D) : SumRepresentations.ReducedParameterProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  intro i σ hσ
  obtain ⟨P, hP⟩ := th i σ hσ
  obtain ⟨Pa, hPa⟩ := a1 i P
  obtain ⟨Sig, h1, h2⟩ := GlobalTheory.T.row_param_of_thetaLift_baseChange D t0 a3 a4 a5 i σ P Pa hP hPa (_root_.GlobalTheory.T.twisted_mu_piece_mem_base_change D t0 a3 a5 a7 s hk i σ P Pa hσ hP hPa)
  refine ⟨⟨⟨_, (l i σ).2 hσ, (l i σ).1⟩, P, hP⟩, Sig, h1, fun P' hP' => ?_⟩
  obtain rfl : P = P' := by
    by_contra hne
    exact hP.1 (le_bot_iff.1 ((le_inf hP.2 hP'.2).trans ((D.naut.typeV_indep i).pairwiseDisjoint hne).le_bot))
  exact h2
end GlobalTheory.NRows.Parts
end
