module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevels
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_fixed_by_local_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AdaptLev.fixed_of_levelOf) | (exact GlobalTheory.Cong.AdaptLev.fixed_of_levelOf) | (intros; apply GlobalTheory.Cong.AdaptLev.fixed_of_levelOf  <;> assumption)
