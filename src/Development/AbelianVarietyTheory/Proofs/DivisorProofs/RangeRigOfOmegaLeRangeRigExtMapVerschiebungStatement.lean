module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebung
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

@[expose] public section

open GlobalTheory

theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung'
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.range (PDivGroup.frobTwist h G).rigOfOmega ≤
      LinearMap.range (PDivGroup.rigExtMap (PDivGroup.verschiebung h G)) :=
  PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung p K h G
