module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatibleStatement

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isRec_of_isRecLit : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  intro hDZ hDI hEx hLM hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h rc H
  obtain ⟨a, ha, ε, hε, L⟩ := H
  refine ⟨a, ha, ε, hε, ?_⟩
  exact
    { bij := L.bij, dim := L.dim, one := L.one, eps := L.eps, cusp := L.cusp, langlands := L.langlands,
      twist := L.twist, central := L.central, dual := L.dual,
      det := GlobalTheory.T.determinant_rec_compatible hSC E Ω A w h a ha _ rc L
      prod := GlobalTheory.T.twist_rec_compatible hEx hLM hSC E Ω A w h a ha _ rc L
      supp := GlobalTheory.T.central_character_rec_compatible hEx hZP hGL hBZ E Ω A w h a ha _ rc L
      sph := GlobalTheory.T.l_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      sat := GlobalTheory.T.epsilon_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      depth := GlobalTheory.T.conductor_rec_compatible hDZ hDI hEx hZP hGL hBZ E Ω A w h rc ⟨a, ha, ε, hε, L⟩ }

end GlobalTheory.LocLanglands
