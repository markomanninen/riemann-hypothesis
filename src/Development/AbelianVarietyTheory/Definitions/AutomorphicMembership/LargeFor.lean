module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
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
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

end GlobalTheory.ShFam
