module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_matrixRep_continuous_crystalline : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  first | exact @GlobalTheory.HTW.Rec.tateDual_matRep_crys | exact GlobalTheory.HTW.Rec.tateDual_matRep_crys | (intros; apply GlobalTheory.HTW.Rec.tateDual_matRep_crys <;> assumption)
