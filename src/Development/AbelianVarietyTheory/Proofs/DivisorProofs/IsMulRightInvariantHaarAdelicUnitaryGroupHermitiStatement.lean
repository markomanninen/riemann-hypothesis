module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.DataExtra

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure <;> assumption)
