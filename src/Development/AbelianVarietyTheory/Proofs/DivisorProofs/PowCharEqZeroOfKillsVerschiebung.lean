module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem frobProj_frobTwist_app {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (x : (frobTwist h G).A n) :
    ((frobProj h G).frobTwist h h).app n x = (frobProj h (frobTwist h G)).app n x := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, SemiHom.frobTwist_app_frobProj]

private theorem frobProj_app_verschiebung {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (a : G.A n) :
    (frobProj h (frobTwist h G)).app n ((verschiebung h G).app n a) =
      (verschiebung h (frobTwist h G)).app n ((frobProj h G).app n a) := by
  refine Test.mulP_injective (frobTwist h (frobTwist h G)) n ?_
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← PDivGroup.res_app, ← SemiHom.res_app, ← SemiHom.res_app, ← PDivGroup.res_app,
    mulP_res, mulP_res, ← map_mulBy, ← SemiBialgHom.map_mulBy ((frobProj h G).app (n + 1)),
    ← relFrob_app_verschiebung_app h G, frobProj_app_relFrob_app,
    ← relFrob_app_frobProj h (G := frobTwist h G) (n + 1),
    ← prime_smul_id_app, ← verschiebung_comp_relFrob]
  rfl

theorem pow_char_eq_zero_of_verschiebung (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n))
    (hχ : ∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) : χ ^ p = 0 := by
  refine CartierDual.ext_apply fun y => ?_
  induction y using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
  | h1 r a =>
    rw [map_smul, ← frobTwistDual_verschiebung h (G := frobTwist h G) n χ,
      ← frobProj_app_verschiebung h G,
      frobTwistDual_frobProj, hχ, zero_pow (Fact.out : p.Prime).ne_zero, smul_zero]
    rfl

end GlobalTheory.PDivGroup
