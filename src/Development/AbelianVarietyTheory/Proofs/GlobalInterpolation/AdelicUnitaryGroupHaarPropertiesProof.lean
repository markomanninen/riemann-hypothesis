module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlacStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomainStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVectorStatement

@[expose] public section

namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ,
    GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular F E σ hσ M J hJ, GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer F E σ hσ M J hJ⟩

end GlobalTheory
