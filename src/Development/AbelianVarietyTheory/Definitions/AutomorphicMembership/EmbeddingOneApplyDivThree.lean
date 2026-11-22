module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.Mem.R3.MjModel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem unitMap_norm (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (x : (unitLat K (Module.finrank ℂ W)).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X
      (InfinitePlace.mk σ) x) = ‖unitMap σ W x‖ := by
  have h1 : unitMap σ W x = ∑ i, σ (x i) • stdOrthonormalBasis ℂ W i :=
    Fintype.linearCombination_apply ℂ (stdOrthonormalBasis ℂ W) (cpt σ x)
  have h2 : ‖unitMap σ W x‖ ^ 2 = ∑ i, ‖σ (x i)‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℂ W).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, (stdOrthonormalBasis ℂ W).orthonormal.inner_right_fintype]
  rw [← Real.sqrt_sq (norm_nonneg (unitMap σ W x)), h2, Formalism.HermitianLatticesTheory.cnorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X (InfinitePlace.mk σ) x i =
      (InfinitePlace.mk σ).embedding (x i) := by
    have h4 : ∀ (n : ℕ) (u : Fin n → ℂ), Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ u = u := fun n u => by
      rw [inv_one, Matrix.one_mulVec]
    exact congrFun (h4 _ _) i
  rw [h3, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

section Record

open Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)

theorem jM_metric_all (hH : Holds R F) (j : ℕ) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => MjCoord.jW_norm Z hH i) (fun _ => unitMap_norm _ _) j x

end Record

end GlobalTheory.Mem.R3.MjModel

end
