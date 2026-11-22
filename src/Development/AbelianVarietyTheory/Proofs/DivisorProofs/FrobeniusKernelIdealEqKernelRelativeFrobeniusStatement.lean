module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

@[expose] public section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
      (G : PDivGroup p R) (n : ℕ),
      frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) :=
  @GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob
