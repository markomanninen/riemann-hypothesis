module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

end Claims

theorem BigC.and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF ((le_max_left _ _).trans hCF)
  obtain ⟨C0', h'⟩ := h' CF ((le_max_right _ _).trans hCF)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  obtain ⟨x0', h'⟩ := h' ε C ((le_max_right _ _).trans hC)
  refine ⟨max x0 x0', fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ⟨?_, ?_⟩⟩
  · exact h D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3
  · exact h' D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3

end GlobalTheory.SumSize

end
