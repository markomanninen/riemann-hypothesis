module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.MovedField Formalism.L2.Host in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    change ((GlobalTheory.FunObj.muBase R.toLevCh j).loc w.1 x : ℂ) *
      ((R.xiH t).loc w.1 x : ℂ) ∈ K
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · exact one_mem K
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · exact one_mem K
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
