module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExtendGenAndCorrOfGenericFibre

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Exist.CubicalExtension

theorem exists_sabMap_of_groupIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K)) (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) (ψ : t.G ≅ t'.G), IsMonHom ψ.hom → m.φ ≫ ψ.hom.left = m'.φ → (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) → ∃ n : SABMap t t' (𝟙 _), n.φ = ψ.hom.left :=
  sabMap_of_iso_of_extendGen GlobalTheory.Exist.extendGen

end GlobalTheory.Exist.CubicalExtension
