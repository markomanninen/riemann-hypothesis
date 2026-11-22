module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVersc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

@[expose] public section

open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K)
    (w : Cot K ((PDivGroup.frobTwist h G).A 1)) :
    ∃ (β : (PDivGroup.frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((PDivGroup.relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((PDivGroup.verschiebung h G).app 1) w' :=
  PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq p K h G w
