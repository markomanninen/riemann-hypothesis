module

public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjLat0
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.Bridge
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.IdealBasis
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

theorem lambda_of_lattice_holds : LamOfLat := by
  intro D cc δ hcc hδ
  exact lattice_ideal_lattice_holds D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc δ hcc hδ




end Formalism.L2.Th1.F2
