module

public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

end Count

section Lat

variable (D : D7)

end Lat

section Num

end Num

section Main

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Main

section Inv

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem c3sub_dual_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.gmap γ M) = Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.dual h M) := by
  have hiso : ∀ x y : V, h (γ x) (γ y) = h x y := fun x y => hγ x y
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.dual E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨γ.symm x, ?_, by simp⟩
    intro m hm
    have hm' := hx (γ m) ⟨m, hm, rfl⟩
    simpa [← hiso m (γ.symm x)] using hm'
  · rintro ⟨z, hz, rfl⟩ y ⟨m, hm, rfl⟩
    have hm' := hz m hm
    simpa [hiso] using hm'

end Inv

section Mean

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Mean

end Formalism.MainNotions.BridgeLemma₂

end
