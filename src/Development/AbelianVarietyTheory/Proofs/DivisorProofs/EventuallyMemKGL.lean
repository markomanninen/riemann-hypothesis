module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Fact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_of {w : Pl E} (g : GL (Fin n) (w.adicCompletion E))
    (h1 : ∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) (h2 : ∀ i j, g⁻¹.1 i j ∈ w.adicCompletionIntegers E) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), ∀ᶠ w : Pl E in cofinite,
      ∀ i j, pLoc E w (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]
    exact fun i j => (g.val i j).2
  filter_upwards [h x, h x⁻¹] with w a b
  exact mem_KGL_of _ a (by rw [← map_inv]; exact b)

end GlobalTheory.EulerTw.Fact
