module

public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop

@[expose] public section

namespace PositivityTheory.Stage1.PM

theorem hermitianHassePrinciple : GlobalTheory.Published.HermitianHassePrinciple :=
  GlobalTheory.Published.hermitianHassePrinciple_holds

theorem thetaRationalInvariance : GlobalTheory.Published.ThetaRationalInvariance :=
  GlobalTheory.Published.thetaRationalInvariance_holds

theorem stoneVonNeumann : GlobalTheory.Published.StoneVonNeumann :=
  GlobalTheory.Published.StoneVonNeumann_holds

end PositivityTheory.Stage1.PM
