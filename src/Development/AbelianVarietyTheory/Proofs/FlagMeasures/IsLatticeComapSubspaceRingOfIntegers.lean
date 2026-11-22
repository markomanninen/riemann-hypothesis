module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Imports
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubtype

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_ne_zero_smul_mem_of_span_eq_top {K V : Type} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.TargetStatementBis.target
  | exact _root_.GlobalTheory.TargetStatementBis.target
  | (apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementBis.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementBis.target ..)

theorem isLattice_comap_subtype_ringOfIntegers {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (W.subtype.restrictScalars (𝓞 K)) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory
