module

public import Mathlib
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible

@[expose] public section

namespace GlobalTheory.DecInputs

theorem decLow_and_decInf_and_kFinSmooth :
    Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth :=
  ⟨GlobalTheory.DecTransport.decLow_holds, Formalism.L2.SG.BesselDiscreteSeries.decInf,
    Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.admitted.kFinSmooth'⟩

end GlobalTheory.DecInputs
