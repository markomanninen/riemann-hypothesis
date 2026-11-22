module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkPointExtensionOfDividedDataStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivGalFix

open GlobalTheory.TorusExt

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkPt_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ q : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ q₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) q₀ q := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD q
  have hB := P.D.tau_bimult
  have ha : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
      (algebraMap (FractionRing R) (FractionRing R)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, hy⟩ := GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase L R hR t P iw s ε e hε hs hD q.y
  let mkIota : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], P.D.toPre.X →+ GtPtF P.D.toPre F := fun F _ _ => by
    open ReciprocityTheory.ChartRestriction.G.DVR in
    exact AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
      obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
      refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have C : IsCub (th P.D.toPre (T := TF (R := R) F) y J) := isCub_cubV P.D.toPre.cub hJ
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
      exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have hi : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x : P.D.toPre.X), GtPtF.IsIota x (mkIota F x) := by
    intro F _ _ x
    exact (exists_iota (F := F) hB x).choose_spec
  have hn : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt P.D.toPre F l.M'), l.M' • p.g = mkIota F p.y := by
    intro F _ _ p
    obtain ⟨h, h₁, h₂⟩ := p.eq
    exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans (isIota_unique h₂ (hi F p.y))
  let mkPt : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (y : P.D.toPre.X) (g : GtPtF P.D.toPre F), l.M' • g = mkIota F y → QkPt P.D.toPre F l.M' := fun F _ _ y g h =>
    ⟨y, g, l.M' • g, (isNsmul_iff_eq _ _ _).2 rfl, h ▸ hi F y⟩
  obtain ⟨p₁, hp₁, -⟩ := existsUnique_qkExt hB _ ha p₀
  have hp₁y : p₁.y = p₀.y := hp₁.1
  have h0 : l.M' • (q.g - p₁.g) = mkIota (AlgebraicClosure (FractionRing R)) 0 := by
    rw [smul_sub, hn, hn, hp₁y, hy, sub_self, map_zero]
  let r := mkPt (AlgebraicClosure (FractionRing R)) 0 (q.g - p₁.g) h0
  obtain ⟨r₀, hr⟩ := GlobalTheory.T.exists_qkPoint_extension_of_divided_data L R hR t P iw s ε e hε hs hD r rfl
  let z := mkPt (FractionRing R) (p₀.y + r₀.y) (p₀.g + r₀.g) (by rw [smul_add, hn, hn, map_add])
  refine ⟨z, ?_⟩
  have hgy : q.y = z.y := by
    change q.y = p₀.y + r₀.y
    have : r₀.y = 0 := by simpa [r, mkPt] using hr.1.symm
    rw [this, add_zero, hy]
  have hgg : q.g = gtExt P.D.toPre _ ha z.g := by
    have hp := (eq_gtExt_iff _ ha _ _).2 hp₁.2
    have hq := (eq_gtExt_iff _ ha _ _).2 hr.2
    change q.g = gtExt P.D.toPre _ ha (p₀.g + r₀.g)
    rw [map_add, ← hp, ← hq]
    change q.g = p₁.g + (q.g - p₁.g)
    abel
  exact ⟨hgy, (eq_gtExt_iff _ ha _ _).1 hgg⟩

theorem qkExt_equiv_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD σ p p' hpp'
  refine GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational R P.D l.M' (fun q => ?_) σ.toAlgHom p p' hpp'
  obtain ⟨q₀, hq⟩ := qkPt_rational L R hR t P iw s ε e hε hs hD q
  exact ⟨q₀, q, hq, qk_equiv_refl P.D.tau_bimult q⟩

end GlobalTheory.DivGalFix
