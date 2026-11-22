module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

@[expose] public section

open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((PDivGroup.relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) :=
  kerIdeal_relFrob_le_frobKerIdeal p R h G n
