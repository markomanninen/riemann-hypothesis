module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  first | exact @GlobalTheory.VacRealForm.differentiable_gZ_top | exact GlobalTheory.VacRealForm.differentiable_gZ_top | (intros; apply GlobalTheory.VacRealForm.differentiable_gZ_top <;> assumption)
