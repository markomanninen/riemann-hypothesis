module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_quotient_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | exact GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adeleE <;> assumption)
