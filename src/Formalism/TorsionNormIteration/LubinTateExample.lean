module

public import Formalism.TorsionNormIteration.InverseIntegralClasses.SolveExistsProof
public import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
public import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
public import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
public import Formalism.TorsionNormIteration.InverseIntegralClasses.NormSigmaLeOne
public import Formalism.TorsionNormIteration.InverseIntegralClasses.MapSubtypeInjective
public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Formalism.TorsionNormIteration.InverseIntegralClasses.IsHomOfSubstEqSmul
public import Formalism.FormalGroupLog.Statement
public import Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd
public import Formalism.TorsionNormIteration.InverseIntegralClasses.LTLemma

@[expose] public section

namespace Formalism.LT

universe u v

theorem funEqSubst : Formalism.G.FunEqSubst.{u, v} :=
  FunEqSubst_of IntegralSubst_proof CoeffBound_valid PowCongr_valid FrobCongr_valid

theorem funEqGroup : Formalism.G.FunEqGroup.{u} :=
  FunEqGroup_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

theorem funEqHom : Formalism.G.FunEqHom.{u} :=
  FunEqHom_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

end Formalism.LT
