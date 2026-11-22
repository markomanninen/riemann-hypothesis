module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

namespace GlobalTheory.KerCalc

attribute [local instance] Over.cartesianMonoidalCategory

theorem evc_pow_left {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left}
    (hP : P.IsLB) (h : IsAdditive P) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    evc hP (a ^ n) b = n • evc hP a b := by
  induction n with
  | zero => rw [pow_zero, zero_smul, h.evc_one hP]
  | succ n ih => rw [pow_succ, (isAdditive_iff hP).1 h, ih, succ_nsmul]

end GlobalTheory.KerCalc
