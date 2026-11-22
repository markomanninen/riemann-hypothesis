module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
public import Formalism.LocalToGlobal.BesselHermitianTheta.Joints
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

structure AllTied (D : D7) (X : ThetaX D) (A : TH.ProvA) where

  T : ThetaTied D X

  sm : ThetaSmoothnessCondition T

  ty : TypTied T

  W : WeilTied D X T
  unr : WeilUnramifiedCondition W

  kf : KfinTied W

  phiUp : PhiYupTied W

  B : BesselTied D X T W

  real : RealTied D

  prov : ProvisionCompatibility D A

end Formalism.L2.Theta

end
