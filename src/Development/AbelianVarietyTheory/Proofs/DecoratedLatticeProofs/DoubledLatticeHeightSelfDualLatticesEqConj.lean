module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdelicConjSelfDualDoublingCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem hgtL_eq_conj_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ g, hgtL A L' a g = hgtL A L a (k⁻¹ * g * k) := by
  intro D A L L' hL hL'
  obtain ⟨k, hk, hK⟩ := GlobalTheory.T.exists_finiteAdelic_conj_selfDual_doublingCompact D A L L' hL hL'
  refine ⟨k, hk, fun a ha g => ?_⟩
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L hL
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L' hL'
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L' a hL' ha
  have hj : io A (k, k) ∈ siegel A := (io_mem_siegel A).2 rfl
  obtain ⟨p, κ, hκ, hx⟩ := hI (io A (g, 1))
  have hκ' : (io A (k, k))⁻¹ * κ * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := (hK a κ).1 hκ
  have e : io A (k⁻¹ * g * k, 1) =
      ((⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) : GA D (dblSp A)) *
        ((io A (k, k))⁻¹ * κ * io A (k, k)) := by
    have h1 : io A (k⁻¹ * g * k, 1) = (io A (k, k))⁻¹ * io A (g, 1) * io A (k, k) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      simp
    rw [h1, hx]
    simp [mul_assoc]
  change hgtAd _ _ L' a (io A (g, 1)) = hgtAd _ _ L a (io A (k⁻¹ * g * k, 1))
  rw [hx, e]
  calc
    hgtAd _ _ L' a (↑p * κ) = _ := hgtAd_mul (isCMExt_host D) p hκ
    _ = _ := by
      congr 1
      rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    _ = hgtAd _ _ L a (↑(⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) *
        ((io A (k, k))⁻¹ * κ * io A (k, k))) :=
      (hgtAd_mul (isCMExt_host D) _ hκ').symm

end GlobalTheory.Core.Rk.IP
