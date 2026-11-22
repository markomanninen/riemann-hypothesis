module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieField

theorem exists_isLieBasis_field : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (g : ℕ),
    SmoothOfRelativeDimension g B.hom → ∃ y : Fin g → (epsR K ⟶ B), IsLieBasis y :=
  fun _ _ B _ _ _ hdim => GlobalTheory.KeyPow.exists_isLieBasis B hdim

end GlobalTheory.LieField
