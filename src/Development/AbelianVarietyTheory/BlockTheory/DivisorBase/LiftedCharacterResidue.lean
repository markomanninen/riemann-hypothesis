module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def stabLat (V : HSp D) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ ∀ z, (finHom V k).1.mulVec z ∈ latHat V ↔ z ∈ latHat V}
  one_mem' := ⟨(GfC V).one_mem, fun z => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(GfC V).mul_mem ha hb, fun z => ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ha', hb']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(GfC V).inv_mem ha, fun z => ?_⟩
    rw [← ha' ((finHom V a⁻¹).1.mulVec z), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

def prinLev (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ stabLat V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

variable (T : CoreJ D)

variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

end GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue
