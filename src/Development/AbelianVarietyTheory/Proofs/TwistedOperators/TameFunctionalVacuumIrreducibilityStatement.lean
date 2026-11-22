module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibility
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_functional_vacuum_irreducibility : ∀ D : D7, Irr D := by
  first | exact @GlobalTheory.Irr.irr | exact GlobalTheory.Irr.irr | (intros; apply GlobalTheory.Irr.irr <;> assumption)
