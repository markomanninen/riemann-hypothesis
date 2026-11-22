module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CkModel
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CkTwist

@[expose] public section

namespace CompanionTheory.RgFd

theorem coefPow : CoefPow := coefPow_of CkM.ckModel ckTwist model_functions_multiply

end CompanionTheory.RgFd
