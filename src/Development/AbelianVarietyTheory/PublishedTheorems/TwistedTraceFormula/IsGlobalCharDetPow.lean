module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

@[expose] public section

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.HCChar
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar.Model

end GlobalTheory.HCChar.Model
