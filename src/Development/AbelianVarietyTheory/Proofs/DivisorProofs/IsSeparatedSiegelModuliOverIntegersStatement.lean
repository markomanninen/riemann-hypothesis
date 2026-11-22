module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeparated_siegelModuli_over_integers : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  first | exact @GlobalTheory.SepSiegel.isSeparated_toZ | exact GlobalTheory.SepSiegel.isSeparated_toZ | (intros; apply GlobalTheory.SepSiegel.isSeparated_toZ <;> assumption)
