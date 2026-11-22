module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsLowerMulUpperOfLeadingMinors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovQF

open CategoryTheory.Limits GlobalTheory.FlagCell

theorem finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (K : Type) [Field K] (y : Sp K ⟶ Y) :
    {x : Sp K ⟶ X | x ≫ f = y}.Finite := by
  have hp : IsFinite (pullback.snd f y) := inferInstance
  have : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f y).isoSpec.inv ≫ pullback.snd f y)
  have h4 : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K Γ(pullback f y, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback f y, ⊤) := h4
  refine (Set.finite_range fun σ : Γ(pullback f y, ⊤) →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pullback f y).isoSpec.inv ≫ pullback.fst f y).subset fun x hx => ?_
  let s : Sp K ⟶ pullback f y := pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (s ≫ (pullback f y).isoSpec.hom)
  have e : φ ≫ σ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hφ, Spec.map_id, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _)
  refine ⟨⟨σ.hom, fun a => congr($e a)⟩, ?_⟩
  show Spec.map σ ≫ _ = _
  rw [hσ, Category.assoc, Iso.hom_inv_id_assoc]
  exact pullback.lift_fst _ _ _

section Sheaves

open GlobalTheory.Twist (resM resM_resM app_resM)

end Sheaves

section Matrices

variable {L : Type} [Field L] {m : ℕ}

end Matrices

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R K L : Type} [CommRing R] [Field K] [Field L]

variable {F : Type} [Field F] {e : F ≃+* c.F}

end Frames

section Points

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}
  (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z}
  {u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB} {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Bs}
  {fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)}
  {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ Y₀} {πG : G ⟶ (O.var c).X} {φ : (O.var c).Fn →+* G.functionField}
  {jG : G ⟶ Bg}

end Points

end GlobalTheory.FlagCovQF

end
