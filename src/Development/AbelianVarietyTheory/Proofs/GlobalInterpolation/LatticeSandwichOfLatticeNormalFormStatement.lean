module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSandwich_of_latticeNormalForm : ∀ (X : Fields) (Pr : Primes X) (R : Ranks), GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R := by
  first | exact @GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | exact GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | (intros; apply GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt <;> assumption)
