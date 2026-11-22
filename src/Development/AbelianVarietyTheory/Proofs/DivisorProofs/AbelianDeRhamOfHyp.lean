module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatementsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDualStatement

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_of_crystallineSmoothLift : GlobalTheory.Published.CrystallineSmoothLift →
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  intro hL hH hC hD hP
  obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ := GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements hL hH
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hhodge, hbc,
    GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
    GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual hC hD hP hF⟩

end GlobalTheory
