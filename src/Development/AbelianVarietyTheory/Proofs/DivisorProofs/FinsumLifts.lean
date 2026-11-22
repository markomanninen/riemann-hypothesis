module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommon
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.CoverHt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem isPreimmersion_j : IsPreimmersion V.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h


end GlobalTheory.Mean4O.CoverHt
