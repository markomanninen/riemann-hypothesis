module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne
    (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h₁ : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (h₂ : q' ≫ q = (p : ℤ_[p]) • 𝟙 H)
    (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1)) (he : GlobalTheory.Dieu.HasLogDeg q e) :
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
      e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) :=
  GlobalTheory.Dieu.le_colength_of_htOne p T k G H q q' e h₁ h₂ hF he
