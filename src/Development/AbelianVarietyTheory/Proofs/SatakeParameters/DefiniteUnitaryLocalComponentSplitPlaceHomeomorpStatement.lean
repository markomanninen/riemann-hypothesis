module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorp
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  first | (exact @GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (exact GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (intros; apply GlobalTheory.Cong.cLoc_locU_bijective_open_continuous  <;> assumption)
