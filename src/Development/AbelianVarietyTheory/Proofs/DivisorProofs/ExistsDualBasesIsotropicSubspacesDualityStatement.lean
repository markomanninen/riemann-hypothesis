module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualBasesIsotropicSubspacesDuality
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompactStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanishStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_bases_isotropic_subspaces_duality : ∀ {D : D7} {V : HSp D} (X X' : Submodule D.host.E V.V), X ≠ ⊥ → X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X → X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' → (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) → (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) → ∃ (a : ℕ) (x x' : Fin a → V.V), 0 < a ∧ a ≤ wittIndex V ∧ Submodule.span D.host.E (Set.range x) = X ∧ Submodule.span D.host.E (Set.range x') = X' ∧ LinearIndependent D.host.E (Sum.elim x x') ∧ (∀ i j, V.hD (x i) (x j) = 0) ∧ (∀ i j, V.hD (x' i) (x' j) = 0) ∧ (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) := by
  first | exact @GlobalTheory.IsoDuality.exists_dual_bases | exact GlobalTheory.IsoDuality.exists_dual_bases | (intros; apply GlobalTheory.IsoDuality.exists_dual_bases <;> assumption)
