module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj.SqNum

theorem not_unrAt_alpha_div_beta_over_S₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hw
  have e : alpha G t i j / beta G i j = G.nu t i ((j : ℕ) + 1) := by
    simp only [alpha, beta, GridData.nu]
    exact mul_div_mul_right_eq_div _ _ _
  rw [e, GlobalTheory.LFun.unrAt_iff_of_chrEq (chrEq_nu (G := G) (t := t) (i := i) (j := j) hL) w]
  intro hu
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine (G.ch.lev1 _ hi1 hi2 w hw).2 fun x hx h1 => ?_
  have a1 := (L.C.isMu0 j).tame w x hx h1
  have a2 := hL.xi_tame t w x hx h1
  have a3 := hu x hx
  change ((L.C.mu0 j).loc w x * (L.xiH t).loc w x) *
    ((G.ch.chiH (D.R.m - i)).loc w x)⁻¹ = 1 at a3
  rw [a1, a2, one_mul, one_mul] at a3
  exact inv_eq_one.1 a3

end GlobalTheory.FunObj.SqNum
