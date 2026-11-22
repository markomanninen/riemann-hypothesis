module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineSelfDual

theorem hT_frame (D : D7) (S : HSp D) (u v : S.V) :
    S.hT u v = ∑ i, ∑ j, star (S.frame.equivFun u i) * S.gram i j * S.frame.equivFun v j := by
  conv_lhs => rw [← S.frame.sum_repr u, ← S.frame.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.equivFun_apply, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def selfDualLatticeCoordsInHermitianFrame (D : D7) (S : HSp D) : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap

theorem frameCoords_mem_selfDualLatticeCoords_iff (D : D7) (S : HSp D) (u : S.V) : S.frame.equivFun u ∈ selfDualLatticeCoordsInHermitianFrame D S ↔ u ∈ S.L0 :=
  ⟨fun ⟨z, hz, e⟩ => S.frame.equivFun.injective e ▸ hz, fun hu => ⟨u, hu, rfl⟩⟩

theorem isSelfDualC_selfDualLatticeCoordsInFrame (D : D7) (S : HSp D) : IsSelfDualC S (selfDualLatticeCoordsInHermitianFrame D S) := by
  refine ⟨⟨S.standardTuple_isLattice.fg.map _, ?_⟩, ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · intro y
    obtain ⟨v, rfl⟩ := S.frame.equivFun.surjective y
    have h2 : v ∈ S.L0 ↔ ∀ u ∈ S.L0, S.hT u v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]
      simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
    have h3 : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ b : 𝓞 D.host.E, (b : D.host.E) = z :=
      fun z => Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
    rw [frameCoords_mem_selfDualLatticeCoords_iff, h2]
    constructor
    · rintro H _ ⟨u, hu, rfl⟩
      have := (h3 _).1 (H u hu)
      rwa [hT_frame] at this
    · intro H u hu
      rw [h3, hT_frame]
      exact H _ ⟨u, hu, rfl⟩

end GlobalTheory.LineSelfDual
