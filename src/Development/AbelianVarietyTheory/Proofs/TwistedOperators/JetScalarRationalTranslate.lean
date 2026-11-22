module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
public import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeCoordsRationalPointMulEqCoordMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableThetaLocalSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitary

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : GlobalTheory.MovedKappaEx.UnitAt q a)
    (hub : GlobalTheory.MovedKappaEx.UnitAt q b) : GlobalTheory.MovedKappaEx.UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dite_eq_left hab, dite_eq_left ha', dite_eq_left hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.RatMoveJets
