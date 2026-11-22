module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicWeilRepresentation_with_rules_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilEx D := by
  first | exact @GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation | exact GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation | (intros; apply GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation <;> assumption)
