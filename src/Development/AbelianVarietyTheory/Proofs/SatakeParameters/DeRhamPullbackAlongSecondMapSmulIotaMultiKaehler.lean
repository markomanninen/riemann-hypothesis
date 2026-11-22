module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem

@[expose] public section

set_option autoImplicit false

noncomputable section

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

namespace GlobalTheory.WH.PullCoc

section Gen

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

end Gen

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section J2

variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

theorem mapDR_smul_ιMulti {L : Type} [Field L] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] (b : K) (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      algebraMap K L b • ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  rw [map_smul, algebraMap_smul]
  congr 1
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, mapDR, map1, Function.comp_def,
    KaehlerDifferential.map_D]

theorem deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD (j2 : K →ₐ[ℂ] K') (b : K) (q : ℕ) (v : Fin q → K) :
    pr2L j2 (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      j2 b • ExteriorAlgebra.ιMulti K' q fun j => D ℂ K' (j2 (v j)) := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul_ιMulti (L := K') b q v

end J2

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

