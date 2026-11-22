module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Neg

theorem valAt_inv {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z}
    {f : Z.functionField} (hf : UnitAt (below y) f) : valAt y f⁻¹ = (valAt y f)⁻¹ := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hf
  rw [← map_units_inv, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_units_inv]

end GlobalTheory.LineNorm.Neg
