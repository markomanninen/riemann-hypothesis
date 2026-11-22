module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelTripleAmpleFramesComponent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_triple_ampleFrames_component : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.exists_zon_ampFrames_component | exact GlobalTheory.exists_zon_ampFrames_component | (intros; apply GlobalTheory.exists_zon_ampFrames_component <;> assumption)
