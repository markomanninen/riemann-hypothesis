module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_dualF {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (L : Submodule (𝓞 K) V) : locF 𝔭 (dualF h 𝔭 L) = dualF h 𝔭 L := by
  have hp := h𝔭.isPrime
  refine le_antisymm ?_ (LocF.le_locF 𝔭 _)
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  show ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  have e : h y (algebraMap (𝓞 F) (𝓞 K) t • x) = algebraMap (𝓞 F) (𝓞 K) t • h y x := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, LinearMap.map_smul, algebraMap_smul]
  have h1 := (show ∀ y ∈ L, h y (algebraMap (𝓞 F) (𝓞 K) t • x) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    from htx) y hy
  rw [e] at h1
  obtain ⟨s, hs, hs_mem⟩ := (LocF.mem_locF_iff hp (1 : Submodule (𝓞 K) K) _).1 h1
  have hst : s * t ∉ 𝔭 := fun hm => (hp.mem_or_mem hm).elim hs ht
  refine (LocF.mem_locF_iff hp _ _).2 ⟨s * t, hst, ?_⟩
  simpa only [map_mul, mul_smul] using hs_mem

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
