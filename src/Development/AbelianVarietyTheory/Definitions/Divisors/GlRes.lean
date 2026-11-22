module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace GlobalTheory.HCA

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

abbrev glG : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ := ⊤

abbrev glL : Submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := ⊤

theorem glH : IsExpLieAlgebra (glG E a) (glL E a) := isExpLieAlgebra_top

variable {E a} [_root_.NumberField.IsTotallyComplex E]

def glRes (φ : GA E a → ℂ) (x : GA E a) : glG E a → ℂ := fun y => φ (x * infGL E a y.1)

end GlobalTheory.HCA

end
