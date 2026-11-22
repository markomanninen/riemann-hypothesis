module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm.Chart

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

section Alg

theorem exists_minor_ne_zero {K : Type} [Field K] {m g k : ℕ} (a : Fin m → Fin g → K) (ha : LinearIndependent K a)
    (hk : k ≤ m) : ∃ s, minor a hk s ≠ 0 := by
  classical
  let M : Matrix (Fin k) (Fin g) K := Matrix.of fun l i => a (Fin.castLE hk l) i
  have hM : LinearIndependent K M.row := ha.comp _ (Fin.castLE_injective hk)
  obtain ⟨κ, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite κ := Finite.of_injective b hb
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : φ (minor a hk s) = minor (fun l i => φ (a l i)) hk s := by
  rw [minor, RingHom.map_det]; rfl

end Alg

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Z : Scheme.{0}}
    (v : Sp (DualNumber R) ⟶ Z) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ v = spMap (dualMap (ψ.comp φ)) ≫ v := by
  rw [← Category.assoc, spMap_comp']
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m g : ℕ}

theorem comb_iff {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) (a : Fin m → R)
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ l, a l • tanOf (hu l))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ l, a l • tanOf (hu l))).left := (isComb_iff (fun l => tanOf (hu l)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  exact ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans
    ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h0)

theorem comb_tan {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x u a w) : IsTanAtG t x w :=
  (comb_iff hu a w).1 h ▸ isTan_tv _

theorem sum_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) (c : Fin m → R) :
    ∑ l, c l • tanOf (hu l) = ∑ i, (∑ l, c l • a l) i • tanOf (he i) := by
  have h : ∀ l, tanOf (hu l) = ∑ i, a l i • tanOf (he i) := fun l => tan_ext ((comb_iff he _ _).1 (ha l))
  simp only [h, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem comb_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) {c : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (hw : IsCombAtG t x u c w) : IsCombAtG t x e (∑ l, c l • a l) w := by
  have hu := fun l => comb_tan he (ha l)
  rw [comb_iff he, ← sum_comb he hu ha]
  exact (comb_iff hu _ _).1 hw

end Tan

section Geo

theorem ringHom_ext {S : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    {φ φ' : Γ(S, V) →+* R} (h : spMap φ ≫ hV.fromSpec = spMap φ' ≫ hV.fromSpec) : φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Geo

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}

theorem coord_map {R S : Type} [CommRing R] [CommRing S] (α : A →+* R) (ψ : R →+* S) {a : Fin g → R}
    {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) a w) :
    IsCombAtG t (spMap (ψ.comp α) ≫ x₀) (fun i => spMap (dualMap (ψ.comp α)) ≫ e i) (fun i => ψ (a i))
      (spMap (dualMap ψ) ≫ w) := by
  have := GlobalTheory.LatDRFree.comb_map t ψ h
  simp only [dual_comp] at this
  rwa [← Category.assoc, spMap_comp'] at this

end Coord

end GlobalTheory.LineNorm.Chart

