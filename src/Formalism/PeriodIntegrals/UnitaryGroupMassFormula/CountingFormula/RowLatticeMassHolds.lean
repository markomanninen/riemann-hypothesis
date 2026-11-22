module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perpS_eq_orth (D : D7) (U : Submodule D.host.E (VS D).V) : perpS (VS D) U = orth (VS D) U := by
  ext v
  rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
  rfl

theorem e_mem_perp (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) :
    F0.e a ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso b a
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem X_le_perp (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.X ≤ perpS (VS D) F0.X := by
  unfold FlagG.X
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact e_mem_perp D F0 a

theorem mem_Mof (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x : WbQ D F0) :
    x ∈ Mof D F0 Λ ↔ ∃ a : perpS (VS D) F0.X, (a : (VS D).V) ∈ Λ ∧ Submodule.Quotient.mk a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem mk_eq_mk (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a b : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk a : WbQ D F0) = Submodule.Quotient.mk b ↔ (a : (VS D).V) - b ∈ F0.X := by
  rw [Submodule.Quotient.eq]
  rfl

theorem Mof_fg (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hfg : Λ.FG) : (Mof D F0 Λ).FG := by
  apply Submodule.FG.map
  apply Submodule.fg_of_fg_map_injective ((perpS (VS D) F0.X).subtype.restrictScalars (𝓞 D.host.E))
    Subtype.val_injective
  refine Submodule.FG.of_le hfg ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hy

theorem Mof_span (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hsp : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤) :
    Submodule.span D.host.E (Mof D F0 Λ : Set (WbQ D F0)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  obtain ⟨d, hd, hdm⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hsp (a : (VS D).V)
  have hdE : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd
  have hmem : (Submodule.Quotient.mk (d • a) : WbQ D F0) ∈ Mof D F0 Λ := by
    rw [mem_Mof]
    refine ⟨d • a, ?_, rfl⟩
    rw [Submodule.coe_smul_of_tower]
    exact hdm
  have e : (Submodule.Quotient.mk a : WbQ D F0) =
      (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (Submodule.Quotient.mk (d • a) : WbQ D F0) := by
    rw [← algebraMap_smul D.host.E d a, Submodule.Quotient.mk_smul, smul_smul, inv_mul_cancel₀ hdE, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem Mof_isLattice (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (Mof D F0 Λ) :=
  Submodule.IsLattice.of_fg D.host.E (Mof_fg D F0 Λ hL.fg)

theorem Mof_unimod (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsUnimodular (hWb D F0) (Mof D F0 Λ) := by
  have hsp : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
    by_contra hspan
    obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
    obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
    let μ := ∑ j, star (φ ((VS D).frame j)) • bs j
    have hμ : ∀ v, (VS D).hT μ v = φ v := by
      have key : (VS D).hT μ = φ := by
        apply (VS D).frame.ext
        intro i
        dsimp [μ]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, LinearMap.sum_apply]
        have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
            φ ((VS D).frame j) * (if i = j then 1 else 0) := by
          intro j
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
          congr 1
          rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
          split_ifs <;> simp
        simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      intro v
      rw [key]
    have hμ₀ : μ ≠ 0 := by
      intro h
      apply hφ₀
      ext y
      simpa [h] using (hμ y).symm
    have hline (a : D.host.E) : a • μ ∈ Λ := by
      rw [← hU]
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
      simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
    obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
      (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
    let f := ψ.restrictScalars (𝓞 D.host.E)
    have hmap (x : D.host.E) : x ∈ Λ.map f := by
      refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
      change ψ ((x / ψ μ) • μ) = x
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
    obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 D.host.E)) (hL.fg.map f)
    have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
    have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
      fun h => ha (hinj (h.trans (map_zero _).symm))
    have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
      have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
      rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
        one_mul] at hx
    apply RingOfIntegers.not_isField D.host.E
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
    refine ⟨b, hinj ?_⟩
    rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  show Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ
  apply le_antisymm
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
    induction x using Submodule.Quotient.induction_on with | H a => ?_

    have hint : ∀ l : perpS (VS D) F0.X, (l : (VS D).V) ∈ Λ →
        (VS D).hT (l : (VS D).V) (a : (VS D).V) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro l hl
      have := hx (Submodule.Quotient.mk l) ((mem_Mof D F0 Λ _).2 ⟨l, hl, rfl⟩)
      rwa [hWb_mk] at this
    obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (perpS (VS D) F0.X)
    let f : Λ →ₗ[𝓞 D.host.E] D.host.E :=
      ((VS D).hT (a : (VS D).V)).restrictScalars (𝓞 D.host.E) ∘ₗ Λ.subtype ∘ₗ ρ
    obtain ⟨w, hw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz (VS D).hT (VS D).herm (VS D).nondeg Λ hL.fg
      hsp f

    have hwΛ : w ∈ Λ := by
      rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D) w y, hw y hy]
      have e1 : f ⟨y, hy⟩ = (VS D).hT (a : (VS D).V) ((ρ ⟨y, hy⟩ : Λ) : (VS D).V) := rfl
      rw [e1, ← PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D)]
      exact hint ⟨_, hρX ⟨y, hy⟩⟩ (ρ ⟨y, hy⟩).2

    have hwv : ∀ v ∈ perpS (VS D) F0.X, (VS D).hT (w - (a : (VS D).V)) v = 0 := by
      intro v hv
      obtain ⟨d, hd, hdm⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hsp v
      have hdE : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd
      have hdp : d • v ∈ perpS (VS D) F0.X := by
        rw [← algebraMap_smul D.host.E d v]
        exact Submodule.smul_mem _ _ hv
      have h1 := hw (d • v) hdm
      have e1 : f ⟨d • v, hdm⟩ = (VS D).hT (a : (VS D).V) ((ρ ⟨d • v, hdm⟩ : Λ) : (VS D).V) := rfl
      rw [e1, hρid ⟨d • v, hdm⟩ hdp] at h1
      have h2 : (VS D).hT (w - (a : (VS D).V)) (d • v) = 0 := by
        rw [map_sub, LinearMap.sub_apply, h1]
        simp
      rw [← algebraMap_smul D.host.E d v, LinearMap.map_smul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left hdE

    have hwX : w - (a : (VS D).V) ∈ F0.X := by
      have : w - (a : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X) := by
        rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
        intro v hv
        rw [← perpS_eq_orth] at hv
        rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (S := VS D), hwv v hv, star_zero]
      rwa [PI.ScalarPairDr.W.orth_orth] at this
    have hwp : w ∈ perpS (VS D) F0.X := by
      have e : w = (a : (VS D).V) + (w - (a : (VS D).V)) := by abel
      rw [e]
      exact Submodule.add_mem _ a.2 (X_le_perp D F0 hwX)
    rw [mem_Mof]
    refine ⟨⟨w, hwp⟩, hwΛ, ?_⟩
    rw [mk_eq_mk]
    exact hwX
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_Mof D F0 Λ x).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_Mof D F0 Λ y).1 hy
    rw [hWb_mk]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val (S := VS D) hU hb ha
    exact Submodule.mem_one.2 ⟨o, ho⟩

theorem zbar_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hz : F0.z ∈ Λ) : zbar D F0 ∈ Mof D F0 Λ :=
  (mem_Mof D F0 Λ _).2 ⟨⟨F0.z, z_mem_perp D F0⟩, hz, rfl⟩

theorem zbar_prim (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
    (c : D.host.E) (hc : c • zbar D F0 ∈ Mof D F0 Λ) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  apply hprim
  obtain ⟨a, ha, hae⟩ := (mem_Mof D F0 Λ _).1 hc
  rw [zbar, ← Submodule.Quotient.mk_smul, mk_eq_mk] at hae
  have hzo : F0.z ∈ orth (VS D) F0.X := by
    rw [← perpS_eq_orth]
    exact z_mem_perp D F0
  have hao : (a : (VS D).V) ∈ orth (VS D) F0.X := by
    rw [← perpS_eq_orth]
    exact a.2
  have hcz : c • F0.z = (a : (VS D).V) + -((a : (VS D).V) - c • F0.z) := by abel
  refine ⟨?_, ?_⟩
  · rw [hcz]
    refine Submodule.add_mem_sup ?_ ?_
    · exact ⟨ha, hao⟩
    · exact Submodule.neg_mem _ (by simpa using hae)
  · exact (orth (VS D) F0.X).smul_mem c hzo

theorem row_lattice_mass_holds : RowM := by
  intro D u F0 Λ hrow
  obtain ⟨_, ⟨hL, hU, ⟨hz, _⟩, hconv⟩, _⟩ := hrow
  exact ⟨Mof_isLattice D F0 Λ hL, Mof_unimod D F0 Λ hL hU, zbar_mem D F0 Λ hz,
    zbar_prim D F0 Λ hconv.2⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass_holds : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowM :=
  PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.row_lattice_mass_holds
