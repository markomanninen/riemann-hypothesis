module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

section Witt

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

end GlobalTheory.SWLink

end
