module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SplitHalves

variable {D : D7}

theorem sum_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} [DecidableEq ι] (hP : Places p I P) :
    ∑ i ∈ I.toFinset, GlobalTheory.FinPlLoc.idem D (· = (p i).v) = GlobalTheory.FinPlLoc.idem D P := by
  classical
  rw [← sub_eq_zero]
  apply GlobalTheory.FinPlLoc.eq_zero_of_comp
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.infPart_pair, Finset.sum_const_zero, sub_zero]
  · intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.compAt_idem]
    by_cases hw : P w
    · obtain ⟨j, rfl⟩ := (hP.mem w).1 hw
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (hP.inj h.symm)))
        (fun hj => absurd (List.mem_toFinset.2 (hP.all j)) hj), if_pos rfl, if_pos hw, sub_self]
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h => hw ((hP.mem w).2 ⟨i, h⟩))), if_neg hw, sub_self]

theorem mem_intAt_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  intro D k _ _ _ _ ι p I P hP a
  classical
  have hpr (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
    have he : q.pr q.e = 1 := by rw [← GlobalTheory.FinPl.FrameLat.sec_one, q.pr_sec]
    have h0 : q.e * cA D (q.sec c) = 0 := by
      rw [← cA_cA q.e, ← map_mul, ← GlobalTheory.FinPl.FrameLat.e_mul_sec q c,
        ← mul_assoc, GlobalTheory.FinPl.FrameLat.cAe_mul_e, zero_mul, map_zero]
    have h1 := congrArg q.pr h0
    rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1
  have hs (q : SplitPt D k) (a : AE D) (t : k) :
      a * q.sec t ∈ intAt D (· = q.v) ↔ q.pr a * t ∈ 𝒪[k] := by
    rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right,
      GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q (GlobalTheory.FinPl.FrameLat.sec_mem_idAt q _),
      hpr, q.pr_sec, and_iff_left (zero_mem _), mul_comm]
  have hcs (q : SplitPt D k) (a : AE D) (t : k) :
      a * cA D (q.sec t) ∈ intAt D (· = q.v) ↔ q.pr (cA D a) * t ∈ 𝒪[k] := by
    have hm : cA D (q.sec t) * a = cA D (q.sec (t * q.pr (cA D a))) := by
      rw [← GlobalTheory.FinPl.FrameLat.sec_mul_right, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA]
    rw [mul_comm, hm, GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q
      (GlobalTheory.FinPl.FrameLat.csec_mem_idAt _), hpr, GlobalTheory.SeeSaw.cA_cA, q.pr_sec,
      and_iff_right (zero_mem _), mul_comm]
  have hsec1 : ∀ i, (p i).sec 1 ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hs (p i) 1 1).2 (by simp)
  have hcsec1 : ∀ i, cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hcs (p i) 1 1).2 (by simp)
  constructor
  · intro h
    have hr := (GlobalTheory.IwaIdeals.mem_intAt_iff.1 h).2
    refine ⟨h.1, fun i => ⟨?_, ?_⟩⟩
    · have h1 : a * (p i).sec 1 ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hsec1 i)).2⟩
      simpa using (hs (p i) a 1).1 h1
    · have h1 : a * cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hcsec1 i)).2⟩
      simpa using (hcs (p i) a 1).1 h1
  · rintro ⟨hid, hh⟩
    refine ⟨hid, ?_⟩
    have ha : a = ∑ i ∈ I.toFinset, (a * (p i).sec 1 + a * cA D ((p i).sec 1)) := by
      conv_lhs => rw [← (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 hid, ← sum_idem hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      set ε := GlobalTheory.FinPlLoc.idem D (· = (p i).v)
      have h1 : ε * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
      have h2 := (GlobalTheory.FinPl.FrameLat.idem_iff (p i) _).1 h1
      have he : ε * (p i).sec 1 = (p i).sec 1 :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _)
      have hce : ε * cA D ((p i).sec 1) = cA D ((p i).sec 1) :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1)
      rw [GlobalTheory.FinPl.FrameLat.sec_one] at he hce ⊢
      calc ε * a = ((p i).e + cA D (p i).e) * (ε * a) := h2.symm
        _ = (ε * (p i).e) * a + (ε * cA D (p i).e) * a := by
          rw [add_mul, mul_left_comm, ← mul_assoc, mul_left_comm (cA D (p i).e), ← mul_assoc]
        _ = a * (p i).e + a * cA D (p i).e := by rw [he, hce, mul_comm (p i).e, mul_comm (cA D (p i).e)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_add (f := _)]
    exact add_mem ((hs (p i) a 1).2 (by simpa using (hh i).1)).2
      ((hcs (p i) a 1).2 (by simpa using (hh i).2)).2

end GlobalTheory.FinPl.SplitHalves

end
