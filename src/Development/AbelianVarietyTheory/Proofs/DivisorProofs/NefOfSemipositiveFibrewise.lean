module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibrStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
  GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefGeneric

theorem ratDeg_nonneg : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q),
    IsArithVar q 1 → ArInt.NefFib L → 0 ≤ ratDeg q L.B := by
  intro k _ W q L hW hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1, e2⟩ := GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective k W q 1 hW 2 L.B L.isLB
  obtain ⟨hproj, hdim⟩ := GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one k W q hW 2
  letI := GlobalTheory.algebraΓOfHom
    (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod 2))))
  have h := GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod 2 _ hproj hdim _ (LB.isLB_pull L.isLB _)
    (fun Z i _ _ _ hZ => GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres k W q L 2 hL Z i hZ)
  rw [ratDeg, degOfRank, ← e1, ← e2]
  simpa [degOfRank] using h

end GlobalTheory.NefGeneric

end
