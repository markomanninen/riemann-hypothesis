module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem intCast_comp_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    (n : End A).asHom ≫ u = n • u := by
  rw [← zsmul_one]
  change (n • 𝟙 A) ≫ u = n • u
  rw [Preadditive.zsmul_comp, Category.id_comp]

theorem comp_intCast_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    u ≫ (n : End B).asHom = n • u := by
  rw [← zsmul_one]
  change u ≫ (n • 𝟙 B) = n • u
  rw [Preadditive.comp_zsmul, Category.comp_id]

theorem charpoly_eq_of_isogeny_intertwines :
    ∀ (K : Type) [Field K] (A B : AbVar K) (u : A ⟶ B) (f : End A) (g : End B),
      IsIsogeny u → f.asHom ≫ u = u ≫ g.asHom → charpoly f = charpoly g := by
  intro K _ A B u f g hu hfg
  obtain ⟨hdim, -, hpos, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B u hu
  have key : ∀ n : ℤ, deg ((n : End A) - f).asHom = deg ((n : End B) - g).asHom := by
    intro n
    have hc : ((n : End A) - f).asHom ≫ u = u ≫ ((n : End B) - g).asHom := by
      rw [End.sub_asHom, End.sub_asHom, Preadditive.sub_comp, Preadditive.comp_sub,
        intCast_comp_cpisog, comp_intCast_cpisog]
      exact congrArg (n • u - ·) hfg
    have h1 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A A B
      ((n : End A) - f).asHom u rfl hdim).2
    have h2 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A B B
      u ((n : End B) - g).asHom hdim rfl).2
    rw [hc, h2, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have hg : IsCharpoly g (charpoly f) := ⟨hm, by rw [hd, hdim], fun n => by rw [hev n, key n]⟩
  exact (GlobalTheory.T.abelianVarietyEndCharpoly_spec K B g).2 _ hg

end GlobalTheory.AV.AbVar
