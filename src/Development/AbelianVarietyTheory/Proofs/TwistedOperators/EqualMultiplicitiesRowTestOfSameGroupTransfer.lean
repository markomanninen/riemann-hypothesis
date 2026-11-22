module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Params
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.R3.DatCopy

noncomputable section

namespace GlobalTheory.Twist

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
theorem multEq_rowTest_of_copy :
    ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px)
      (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b)
      (z : Dat a.st I hX Tw Wt),
      let z' := GlobalTheory.Mem.R3.DatCopy.copy b s z
      (GlobalTheory.CuspMult.MultEq z'.R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧
        (Formalism.IndefR.Rat.RowTest (z'.R.toCx3 z'.F) →
          Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) := by
  intro B C a b px I hX Tw Wt s z
  have e := twice_eq b (iK := z.alg) z.R
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := multEq_tr (a := b) a (iK := alg b z.alg) (R := real b z.R.toRealDat)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2
  · have h2 := rowTest_tr (a := b) a (iK := alg b z.alg) (R := real3 b z.R) (F := face3 b z.F)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2

end GlobalTheory.Twist

end
