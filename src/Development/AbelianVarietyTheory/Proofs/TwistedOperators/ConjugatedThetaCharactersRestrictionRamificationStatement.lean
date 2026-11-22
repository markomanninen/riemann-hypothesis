module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => GlobalTheory.ConjSplitChars.unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => GlobalTheory.ConjSplitChars.unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine GlobalTheory.ConjSplitChars.tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩
