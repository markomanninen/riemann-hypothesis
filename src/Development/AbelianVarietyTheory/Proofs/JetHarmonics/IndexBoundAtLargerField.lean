module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

noncomputable def coordMap {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : C →ₗ[F] (Fin n → K) :=
  ((z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)).restrictScalars F).comp (TensorProduct.mk F K C 1)

theorem coordMap_linearIndependent {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (m : ℕ) (b : Fin m → C) (hb : LinearIndependent F b) :
    LinearIndependent K fun a => coordMap z (b a) :=
  (Module.Flat.linearIndependent_one_tmul (S := K) hb).map' (z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)) z.symm.ker

theorem coordMap_span {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : Submodule.span K (Set.range (coordMap z)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end GlobalTheory.FormTies
