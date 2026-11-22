module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem det_unitary_adelic_point_gram_step_norm_one : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Matrix.GeneralLinearGroup.det x.1 ∈ Formalism.L2.DIV.U1 (sigD D) := by
  intro D i hi x
  exact Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2

end GlobalTheory.TwV
