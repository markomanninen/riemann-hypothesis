module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamFEOneOfPsiRel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionFieldStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU

theorem fe_one_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U θ f hθ hψ t s hts
  obtain ⟨hp, hq⟩ := PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hp θ
  obtain ⟨s₀, hs₀, -⟩ := hq f
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expF_of_theta_degree_one h₁ h₂ V hV D A G U θ f hθ th s₀ hth hs₀).2.2 t s hts
  exact famFE_one_of_psiRel h₁.globalFns V D (Kbar V) s₀ s c (GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field V D (Kbar V) f s₀ hs₀ hψ) hc

end GlobalTheory.UU
end
