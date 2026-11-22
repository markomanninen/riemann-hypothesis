module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D := by
  first | exact @GlobalTheory.InertAll.inertAllO | exact GlobalTheory.InertAll.inertAllO | (intros; apply GlobalTheory.InertAll.inertAllO <;> assumption)
