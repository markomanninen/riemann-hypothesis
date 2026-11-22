module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem exists_dat_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f = c.1 →
    ∀ g : Fn2 A, IsAdd (fv f) g → ∃ d : Dat t c, d.f = f ∧ d.g = g := by
  intro R _ A _ p G t c f hf g hg
  choose liftRes liftRes_spec using fun n ↦ G.res_surjective n
  let value (n : ℕ) : G.A n :=
    fv f (G.A (n + 1)) (G.A n) (G.res n).toAlgHom (t.y (n + 1))
  let h : ∀ n, G.A n := Nat.rec (motive := G.A) 0 (fun n a ↦ liftRes n (a - value n))
  refine ⟨⟨f, hf, g, hg, h, ?_⟩, rfl, rfl⟩
  intro n
  have hres : G.res n (h (n + 1)) = h n - value n := liftRes_spec n _
  change value n = h n - G.res n (h (n + 1))
  rw [hres, sub_sub_cancel]

end GlobalTheory.PtExt
