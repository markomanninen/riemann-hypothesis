module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAdditiveCharacterEqAdelic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_additive_character_eq_adelic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E), psiAt w x = (localAdelicChar E w x : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar | exact GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar | (intros; apply GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar <;> assumption)
