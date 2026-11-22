module

public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.TateThesis.HeckeTheorem
public import GroundTheory.GlobalFields.TateThesis.Nonvanishing
public import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar partialLFunction coe_localChar continuous_localChar)
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.HeckePartial

end GlobalTheory.CompanionTheory.HeckePartial

end
