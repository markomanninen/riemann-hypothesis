module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg

@[expose] public section

open Formalism.BasicNotions Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem vacuum_oriented_exists : ∀ D : D7, VacExistsO D := GlobalTheory.VacuumO.vacExists

end GlobalTheory.Member
