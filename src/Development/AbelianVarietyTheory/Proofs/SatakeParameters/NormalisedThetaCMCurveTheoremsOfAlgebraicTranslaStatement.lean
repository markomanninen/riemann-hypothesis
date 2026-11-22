module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTransla
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates : Formalism.L2.KerInert.AlgTAll → GlobalTheory.ThLoc.Inputs := by
  first | exact @GlobalTheory.ThLoc.inputs_of_algT | exact GlobalTheory.ThLoc.inputs_of_algT | (intros; apply GlobalTheory.ThLoc.inputs_of_algT <;> assumption)
