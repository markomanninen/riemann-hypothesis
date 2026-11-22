module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PosNear
public import Formalism.PeriodIntegrals.VolFromSW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.WeilQuotMeas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq

@[expose] public section

noncomputable section

namespace PI.VolStabSW

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

end Loc

end CompGAux

end PI.VolStabSW
