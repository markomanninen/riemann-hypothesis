module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Theory

variable {p : ℕ} [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def redVToRange (G : PDivGroup p k) : T.M G →+ LinearMap.range G.rigOfOmega :=
  AddMonoidHom.codRestrict ((T.red G).toAddMonoidHom.comp (T.V G).toAddMonoidHom)
    (LinearMap.range G.rigOfOmega) fun m =>
      ((GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).1 (T.red G (T.V G m))).1 ⟨m, rfl⟩

def theta (G : PDivGroup p k) : T.M G →+ G.omega :=
  (LinearEquiv.ofInjective G.rigOfOmega (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2).symm.toLinearMap.toAddMonoidHom.comp
    (T.redVToRange G)

theorem rigOfOmega_theta (G : PDivGroup p k) (m : T.M G) :
    G.rigOfOmega (T.theta G m) = T.red G (T.V G m) := by
  have inj := (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2
  exact LinearEquiv.ofInjective_symm_apply G.rigOfOmega (h := inj) (T.redVToRange G m)

theorem theta_spec (G : PDivGroup p k) :
    (∀ m, G.rigOfOmega (T.theta G m) = T.red G (T.V G m)) ∧ Function.Surjective (T.theta G) ∧
      (∀ m, T.theta G m = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ (a : WittVector p k) (m : T.M G), T.theta G (WittVector.frobenius a • m) =
        WittVector.constantCoeff a • T.theta G m) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.theta G (T.map f m) = omegaMap G H f (T.theta H m) := by
  have hG := GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G
  have inj := hG.2.2.2
  refine ⟨T.rigOfOmega_theta G, fun w => ?_, fun m => ?_, fun a m => ?_, fun H f m => ?_⟩
  · obtain ⟨m, hm⟩ := (hG.1 (G.rigOfOmega w)).2 ⟨w, rfl⟩
    exact ⟨m, inj ((T.rigOfOmega_theta G m).trans hm)⟩
  · calc
      T.theta G m = 0 ↔ G.rigOfOmega (T.theta G m) = 0 :=
        ⟨fun h => (congrArg G.rigOfOmega h).trans (map_zero G.rigOfOmega),
          fun h => inj (h.trans (map_zero G.rigOfOmega).symm)⟩
      _ ↔ ∃ n, m = T.F G n := (congrArg (· = 0) (T.rigOfOmega_theta G m)).to_iff.trans (hG.2.1 m)
  · apply inj
    have hV : T.V G (WittVector.frobenius a • m) = a • T.V G m := by
      rw [(T.V G).map_smulₛₗ]
      change (WittVector.frobeniusEquiv p k).symm (WittVector.frobeniusEquiv p k a) • T.V G m = _
      rw [RingEquiv.symm_apply_apply]
    simpa only [T.rigOfOmega_theta, G.rigOfOmega.map_smul, hV] using!
      (T.red G).map_smulₛₗ a (T.V G m)
  · apply inj
    have hV := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).2.2.2.2 H f m
    have hred : T.red G (T.map f (T.V H m)) = rigExtMap f (T.red H (T.V H m)) :=
      T.base.red_map trivial trivial f (T.V H m)
    rw [T.rigOfOmega_theta, ← hV, hred, ← T.rigOfOmega_theta H m, rigExtMap_rigOfOmega]

end GlobalTheory.Dieu.Theory

theorem GlobalTheory.Dieu.theta_exists :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type)
      [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega, ∀ G : PDivGroup p k,
        (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧ Function.Surjective (θ G) ∧
        (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
        (∀ (a : WittVector p k) (m : T.M G),
          θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
        ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
          θ G (T.map f m) = omegaMap G H f (θ H m) :=
  fun _ _ T _ _ _ _ => ⟨fun G => T.theta G, fun G => T.theta_spec G⟩
