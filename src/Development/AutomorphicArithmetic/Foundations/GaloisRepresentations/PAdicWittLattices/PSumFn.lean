module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dite_eq_left a, dite_eq_left hh]
  simp only [e]
