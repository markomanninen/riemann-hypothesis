module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

@[expose] public section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
      (G : PDivGroup p R) (a : G.A 1),
      (verschiebung h G).app 1 a = 0 →
        G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) :=
  @GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero
