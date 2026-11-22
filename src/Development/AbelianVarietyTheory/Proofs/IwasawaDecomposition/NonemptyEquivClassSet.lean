module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
public import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.Divisibility.PrinLevClass
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalRingCardinality.DataExtra
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LevPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Comp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

end Comp

section Abstract

end Abstract

section Classes

open GlobalTheory.Mass Formalism.IndefR.Lev Formalism.L2.DIV

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

end Classes

section Local

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

theorem mem_hatL_iff [Module.Finite (𝓞 E) Λ] (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z ∈ hatL (F := F) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (z i)) ∈ locL v Λ :=
  mem_latS_adele_iff Λ z

end Local

section LocalLevel

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (Λ : Submodule (𝓞 E) (Fin S.rank → E))

variable {hc S gp Λ}

end LocalLevel

section Level

open Formalism.L2.Geo.Def Formalism.IndefR.Lev Formalism.L2.DIV
open Formalism.UG (levelVL levelAfL prV bc stabGL)

variable (D)

variable {D}

end Level

end GlobalTheory.LevPin
