module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

theorem exists_unipB_mul_diagT_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  intro k _ _ _ _ m g
  obtain ⟨u, l, w, hw, h⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (points (Fin m)) g
  refine ⟨u, u.2, (leviTorus k (Fin m)).symm l, w, hw, ?_⟩
  rw [h]
  simp [diagT]

end GlobalTheory.SmGL
