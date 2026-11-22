module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

@[expose] public section

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {w : PlE D.host}
  (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O)

structure IsDeRhamOf : Prop where
  deRham : IsdRAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)
  jumps : ∀ (τ : D.host.E →+* Qbar l) (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced Bw τ τ' →
    ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      (D.naut.infG π (ι.toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2) ∧
      IsJumpsAt (D.loc l) Bw (resDec D.nd.plOm.1 r w) τ J

def FrobMatch {K : Type} [CommRing K] (φ : K →+* ℂ) (M : G D.host.E D.nd.Om →* GL (Fin a) K) (u : ℝ) : Prop :=
  ∀ᶠ w : PlE D.host in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    (M σ : Matrix (Fin a) (Fin a) K).charpoly.map φ =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) u)).map fun α => X - C α).prod

variable {D ι π s r}

end GlobalTheory.TripleLocal

end
