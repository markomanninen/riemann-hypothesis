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

@[expose] public section

noncomputable section

namespace GlobalTheory.PtSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem map_MjSig_eq (D : D7) (i : D.nd.Loc) (hInt : Rows.IsotInternal D.what₂) (h42 : SumRepresentations.At.Conclusion42 D.nd D.naut i)
    (hUp : ParUpRec D.nd D.naut i) (hDown : DownMemRec D.nd D.naut i) (hNZ : TypeNZRec D.nd D.naut i) :
    ∀ x ∈ ZgoodN D.nd D.naut i, ∀ Sig, HasParamX D.nd D.naut i x Sig →
      (MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = eigC D.nd D.naut i x := by
  intro x hx Sig hS
  refine Submodule.eq_of_le_of_finrank_le (hUp x hx Sig hS) ?_
  have hinj := SumRepresentations.thetaT_injective D.nd D.naut i hInt h42
  have h1 : Module.finrank ℂ ↥((MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i))) =
      Module.finrank ℂ ↥(MjSig D.nd D.naut i Sig) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (MjSig D.nd D.naut i Sig))).symm
  have hfi : Function.Injective ((D.what₂.thetaP (D.nd.mu i) (D.nd.j i)).domRestrict (eigC D.nd D.naut i x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    exact Subtype.ext (hNZ x hx F.1 F.2 hF)
  have h2 : Module.finrank ℂ ↥(eigC D.nd D.naut i x) =
      Module.finrank ℂ ↥((eigC D.nd D.naut i x).map (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))) := by
    rw [← LinearMap.range_domRestrict]
    exact (LinearMap.finrank_range_of_inj hfi).symm
  rw [h1, h2]
  exact Submodule.finrank_mono (hDown x hx Sig hS)

end GlobalTheory.PtSt

end
