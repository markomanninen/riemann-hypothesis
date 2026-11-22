module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

def KerKilledOn (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (V : S'.Opens) : Prop :=
  ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G),
    (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull
        (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen,
        s.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledLocus
