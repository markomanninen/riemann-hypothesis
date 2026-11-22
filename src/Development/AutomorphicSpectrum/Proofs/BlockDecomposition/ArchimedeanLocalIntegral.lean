module

public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
public import GroundTheory.AutomorphicForms.GL2Classical.KFinite
public import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RealArchimedeanCharacter

open Ad3 Ad3.R
open RationalIdeles (realEquiv realUnitsEquiv)

end GlobalTheory.CompanionTheory.RealArchimedeanCharacter

end
