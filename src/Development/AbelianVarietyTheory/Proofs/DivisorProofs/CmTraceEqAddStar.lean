module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.TraceAddStar

theorem trace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := by
  intro D x
  exact Formalism.MainNotions.BridgeLemma.tie_trace D.sp.cm x

end GlobalTheory.TraceAddStar
