module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRigExtMapRelFrobLeRangeRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

@[expose] public section

open GlobalTheory GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K),
      LinearMap.ker (rigExtMap (PDivGroup.relFrob h G)) ≤
        LinearMap.range (PDivGroup.frobTwist h G).rigOfOmega :=
  @PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega
