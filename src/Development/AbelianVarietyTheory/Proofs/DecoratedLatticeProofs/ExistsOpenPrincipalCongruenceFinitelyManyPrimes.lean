module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelOpen

theorem exists_open_princ : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V β Z
  have hOpen : IsOpen (((Kg D.sp.cm V.gram β Z).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    set N : ℕ := ∏ PP ∈ Z, Ideal.absNorm PP.asIdeal with hN
    have hN0 : 0 < N := Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
    have hNm : ∀ PP ∈ Z, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hP => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
      rw [hN, hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    let P : GA D V → Prop := fun k => ∀ i j, ∃ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (β⁻¹ * Lev.finE V k * β).1 i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j = N • s
    have hP : ∀ᶠ k in nhds (1 : GA D V), P k := by
      have hc := (GlobalTheory.Member.continuous_finHom_val D V).tendsto 1
      rw [map_one, Units.val_one] at hc
      exact hc.eventually (GlobalTheory.DefiniteEnd.eventually_cong β N hN0)
    have hP' : ∀ᶠ k in nhds (1 : GA D V), P k⁻¹ := by
      have : Filter.Tendsto (fun k : GA D V => k⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv (G := GA D V)).tendsto 1
      exact this.eventually hP
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hP.and hP') ?_)
    rintro k ⟨h1, h2⟩
    obtain ⟨y, hy, hred⟩ := GlobalTheory.DefiniteEnd.exists_int_of_entries _ (β⁻¹ * Lev.finE V k * β) N h1 (by
      rw [show (β⁻¹ * Lev.finE V k * β)⁻¹ = β⁻¹ * Lev.finE V k⁻¹ * β by rw [map_inv]; group]; exact h2)
    have hy' : frGL β y = Lev.finE V k := by
      show β * Formalism.UG.bc _ y * β⁻¹ = _
      rw [hy]; group
    have hSt : Lev.finE V k ∈ St β := ⟨y, hy'⟩
    refine ⟨⟨GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k), hSt⟩, ?_⟩
    refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hSt, ?_⟩
    rw [← hy', redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hNm PP hP)
  
  refine ⟨_, hOpen, fun k hk => ?_⟩
  have hk' : Lev.finE V k ∈ Kg D.sp.cm V.gram β Z := hk
  have h1 : Lev.finE V k ∈ ⨅ PP ∈ Z, princAt β PP := hk'.2
  refine ⟨hk'.1.2, fun PP hP => ?_⟩
  exact (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2

end GlobalTheory.ChainOnto.LevelOpen
