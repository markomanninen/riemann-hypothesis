module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_closed_system_coherent : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | exact GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | (intros; apply GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr <;> assumption)
