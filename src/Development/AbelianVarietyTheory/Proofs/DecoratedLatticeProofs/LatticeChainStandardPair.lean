module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDiscriminantTwelfthRootOfIdeal
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLineStd

theorem aaOf_top (D : D7) : (Formalism.L2.PairingIndexBounds.F.aaOf D ⊤) = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  GlobalTheory.Mem.Col2.Th.perAA_top D.host

end GlobalTheory.ThetaLineStd
