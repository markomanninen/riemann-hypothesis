module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotPairedId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_rapidDecay : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.CuspRapidDecaySiegelGL → GlobalTheory.Published.GelfandKazhdanDual := by
  intro hJS hAF hRD E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  · obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre E n hn π
    have hp := GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ
    have h := GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹
    rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GelfandKazhdanTop
