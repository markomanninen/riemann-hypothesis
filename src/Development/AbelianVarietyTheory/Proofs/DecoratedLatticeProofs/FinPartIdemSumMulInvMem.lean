module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumInt

theorem finPart_idemSum_mul_inv_mem : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ t : 𝓞 D.host.E, (∀ Q ∈ SS, t ∉ Q.asIdeal) → finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D := by
  intro D e SS hS t ht
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hS
  by_cases h0 : t = 0
  · subst h0
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ fun PP hPP => ?_
      by_contra hn
      exact ht PP hPP (((hes PP hPP).2 t h0).2 hn)

end GlobalTheory.IdemSumInt
