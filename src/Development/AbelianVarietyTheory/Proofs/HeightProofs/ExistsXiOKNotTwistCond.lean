module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
public import Formalism.LocalRingCardinality.HostCls

@[expose] public section

noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin
open scoped TensorProduct

variable {D : D7}

theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

end GlobalTheory.TwistFieldCompare
