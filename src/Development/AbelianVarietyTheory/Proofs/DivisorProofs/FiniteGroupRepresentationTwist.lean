module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexificationStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem typeSubspace_eq_iInf_ker {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] {n : ℕ}
    {Wσ : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) :
    A.typeP J0 lam0 = ⨅ p : J0, LinearMap.ker (A.ρ p - ((A.chi p * lam0 p : LLˣ) : LL) • LinearMap.id) := by
  ext F
  simp [Formalism.IndefR.Arith.FormsL.mem_typeP, Submodule.mem_iInf, sub_eq_zero]


end GlobalTheory.DefRead

namespace GlobalTheory.DefRead


end GlobalTheory.DefRead
