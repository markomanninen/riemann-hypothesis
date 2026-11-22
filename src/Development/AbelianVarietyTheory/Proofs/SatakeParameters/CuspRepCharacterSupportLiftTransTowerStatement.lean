module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTower
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_characterSupportLift_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  first | (exact @GlobalTheory.RoadU.charLift_trans) | (exact GlobalTheory.RoadU.charLift_trans) | (intros; apply GlobalTheory.RoadU.charLift_trans  <;> assumption)
