module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_adeles_local_ring_totally_real : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.isLocR_Ainf | exact GlobalTheory.CompanionTheory.SW.isLocR_Ainf | (intros; apply GlobalTheory.CompanionTheory.SW.isLocR_Ainf <;> assumption)
