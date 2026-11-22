module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.Pst.DmapNonzero

