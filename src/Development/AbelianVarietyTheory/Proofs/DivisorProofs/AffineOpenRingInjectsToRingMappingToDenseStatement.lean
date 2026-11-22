module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDense
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_ring_injects_to_ring_mapping_to_dense : ∀ (X : Scheme.{0}) [IsReduced X] [IsLocallyNoetherian X] (U : X.Opens), Dense (U : Set X) → ∀ (W : X.Opens) (hW : IsAffineOpen W), ∃ (K : Type) (_ : CommRing K) (ρ : Γ(X, W) →+* K), Function.Injective ρ ∧ ⊤ ≤ (spMap ρ ≫ (show Sp Γ(X, W) ⟶ X from hW.fromSpec)) ⁻¹ᵁ U := by
  first | exact @GlobalTheory.affineOpen_injects_to_dense | exact GlobalTheory.affineOpen_injects_to_dense | (intros; apply GlobalTheory.affineOpen_injects_to_dense <;> assumption)
