module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlaces
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualFrame_hermitian_form_trace_real_places : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  first | exact @GlobalTheory.DFrame.hOK_vecF | exact GlobalTheory.DFrame.hOK_vecF | (intros; apply GlobalTheory.DFrame.hOK_vecF <;> assumption)
