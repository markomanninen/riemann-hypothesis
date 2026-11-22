module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelLocalSC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.CharTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasSupport_rep_tw {x : IrrGL (k := k)} {s : Multiset (IrrGL (k := k))} (hx : HasSupport x.rep s) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : HasSupport (x.tw χ hχ).rep (s.map (·.tw χ hχ)) :=
  (hx.tw χ hχ).of_equiv (x.twEquiv χ hχ)

theorem chars_tw {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (chars ξ hξ).map (·.tw χ hχ) = chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ := by
  simp only [chars, Multiset.map_map, Function.comp_def, IrrGL.tw_ofChar]

end GlobalTheory.RoadU.CharTwist
