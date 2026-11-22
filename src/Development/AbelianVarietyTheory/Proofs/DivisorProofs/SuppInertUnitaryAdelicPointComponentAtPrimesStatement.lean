module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | exact GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | (intros; apply GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert <;> assumption)
