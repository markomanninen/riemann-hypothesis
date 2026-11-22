module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsPosReal (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

variable {D : D7}




end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

end
