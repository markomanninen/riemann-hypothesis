module

public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapAll

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory

theorem kappaSplit_all : ∀ D : D7, KappaSplit D :=
  fun D => Formalism.L2.Ker.KS.kappaSplit D

end GlobalTheory
