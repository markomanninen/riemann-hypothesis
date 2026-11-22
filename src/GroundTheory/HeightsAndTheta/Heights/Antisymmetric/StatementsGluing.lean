module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

section Lattices

variable {Ω : Type*} [Field Ω]

end Lattices

section Join

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}

def joinPt (x : ι → Ω) (z : κ → Ω') : ι × κ → Ω' :=
  segreJoin (fun i => algebraMap Ω Ω' (x i)) z

end Join

section AddBlock

universe u

def addBlockIdx {K : Type*} (ι : K → Type u) (κ : Type u) : Option K → Type u
  | none => κ
  | some k => ι k

def addBlockPt {K : Type*} {ι : K → Type u} {κ : Type u} {Ω Ω' : Type*} [Field Ω] [Field Ω']
    [Algebra Ω Ω'] (y : (Σ k, ι k) → Ω) (z : κ → Ω') : (Σ o, addBlockIdx ι κ o) → Ω'
  | ⟨none, i⟩ => z i
  | ⟨some k, i⟩ => algebraMap Ω Ω' (y ⟨k, i⟩)

end AddBlock

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights
