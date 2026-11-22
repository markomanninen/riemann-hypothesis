module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdelicDecompositionAtFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_adelic_decomposition_at_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → Y.L.IsFullLattice E → ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) z → ∃ X₀ : Matrix (Fin n) (Fin d) E, z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  first
  | exact @GlobalTheory.LatPtDecomp.decomp
  | intro F E _ _ _ _ _ n d X Y hX hY v z hz
    exact GlobalTheory.LatPtDecomp.decomp F E X Y hX.toIsLattice hY.toIsLattice v z hz
