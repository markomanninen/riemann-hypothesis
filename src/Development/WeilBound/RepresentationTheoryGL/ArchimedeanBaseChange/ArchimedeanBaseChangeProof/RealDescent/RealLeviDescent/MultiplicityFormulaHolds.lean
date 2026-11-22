module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultForOfCapCls
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliClassificationOfActionStatement

@[expose] public section

namespace PositivityTheory.RgBcC.RealD

theorem multiplicity_formula_holds : MultFor :=
  multFor_of_capCls (GlobalTheory.T.capelli_classification_of_action injective_decomposition_action_holds.2.2)

end PositivityTheory.RgBcC.RealD
