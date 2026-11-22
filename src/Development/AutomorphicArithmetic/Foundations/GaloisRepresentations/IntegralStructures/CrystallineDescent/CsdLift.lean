module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CsdScopeOfLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.csdLift_holds :
    CsdLift := by
  intro hJ hG E M _ _ _ _ _ _ _ l a ha π P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  have hreg' : (CG.mk P).IsRegAlg := (CG.isRegAlg_iff _).2 fun τ => by
    rw [hL.inf τ]
    exact (CG.isRegAlg_iff _).1 hreg (τ.comp (algebraMap E M))
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨hreg', ⟨fun v => by rw [locInf_pow, quadChar_locInf], ?_⟩, trivial⟩
  rw [GlobalTheory.CsdLift.compNorm_quadChar_pow]
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P 1 ?_
  have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π _ hpol
  have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
  filter_upwards [(GlobalTheory.LiftPolar.tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hs, B, hB⟩
  rw [GlobalTheory.CsdLift.compNorm_quadChar_pow] at hs
  have e1 := GlobalTheory.LiftPolar.cPl_under (E := E) w
  have e2 := GlobalTheory.LiftPolar.normV_cPl w
  have e3 := GlobalTheory.LiftPolar.normV_cPl (w.under (𝓞 E))
  have hf := GlobalTheory.LiftPolar.normV_under (K := E) w
  set f := w.asIdeal.inertiaDeg (𝓞 E)
  have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
  have h1 := hL.sat w f B hf hB0
  have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
  refine ⟨GlobalTheory.CsdLift.unrAt_one w, _, _, h1, h2, ?_⟩
  simp only [GlobalTheory.CsdLift.val_one, Multiset.map_map, Function.comp_def, mul_one, inv_one, inv_pow, inv_inv]
