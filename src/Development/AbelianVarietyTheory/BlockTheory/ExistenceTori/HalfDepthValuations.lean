module

public import Mathlib
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthPins
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.DIV.Cons

variable {D : D7}



section Rec

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

end Rec

theorem bar_eq_barE (Q : Par D) (a : 𝓞 D.host.E) : Q.H.bar a = barE D a := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact Q.H.bar_eq a

end GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations
