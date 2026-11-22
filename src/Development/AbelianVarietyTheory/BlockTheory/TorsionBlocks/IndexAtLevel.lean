module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

open Formalism.BasicNotions Formalism.MainNotions

variable (D : D7) (u : D.what₂.Word)

def IsScaledU (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (g : (D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub) : Prop :=
  ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (g x : LT.Vl D u 0) =
    (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) •
      LT.Uop D u 0 v ((D.fm u).emb 0 (x : LT.Vl D u 0))

end GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

end
