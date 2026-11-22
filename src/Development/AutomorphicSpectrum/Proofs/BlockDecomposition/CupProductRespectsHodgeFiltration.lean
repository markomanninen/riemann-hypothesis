module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CupdR

theorem dividedPowerFiltration_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r s : ℕ) :
    pdP δ r * pdP δ s ≤ pdP δ (r + s) := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    exacts [hl q h, hl' q h]
  · simp only [List.map_append, List.sum_append]
    omega
  · simp [List.map_append, List.prod_append]

theorem term_mem {b : Base} {L : b.Fun} {p n r : ℕ} (t : ComposableArrows (Thick L) n)
    (f : CH.Cn (CH.modF (thA L)) p) (hf : ∀ s, (show (s.obj (Fin.last p)).B from f s) ∈ (s.obj (Fin.last p)).pdPow r)
    (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    (show (t.obj (Fin.last n)).B from CH.term (CH.modF (thA L)) t f g hg) ∈ (t.obj (Fin.last n)).pdPow r :=
  dividedPowerFiltration_map (t.map (homOfLE (Fin.le_last (g (Fin.last p))))).dp r (hf (hg.functor ⋙ t))

theorem cup_bilinear_filtered {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (i j : ℕ) :
    (∃ b : HdR q i →ₗ[K] HdR q j →ₗ[K] HdR q (i + j), ∀ x y, b x y = cupK q rfl x y) ∧
    ∀ r s, ∀ x ∈ FilR q i r, ∀ y ∈ FilR q j s, cupK q rfl x y ∈ FilR q (i + j) (r + s) := by
  let P := CH.mulP (thA (smFun X q))
  let Q := CrystallineSemistableComparison.Auxff.toCx P
  have cup_eq_local : ∀ x y, P.cup (rfl : i + j = i + j) x y = Q.cup (rfl : i + j = i + j) x y := by
    intro x y
    unfold CrystallineSemistableComparison.CH.Pairing.cup CrystallineSemistableComparison.CxPairing.cup
    split_ifs with hz
    · rfl
    · exact absurd ((Q.leib (rfl : i + j = i + j) _ _).trans (by
        rw [show (CH.cx (CH.modF (thA (smFun X q)))).d i (Quotient.out x).1 = 0 from (Quotient.out x).2,
          show (CH.cx (CH.modF (thA (smFun X q)))).d j (Quotient.out y).1 = 0 from (Quotient.out y).2]
        simp)) hz
  have hb : ∃ b : HdR q i →ₗ[K] HdR q j →ₗ[K] HdR q (i + j), ∀ x y, b x y = cupK q rfl x y := by
    obtain ⟨b, hb⟩ := CrystallineSemistableComparison.Auxff.cx_bilin Q (rfl : i + j = i + j)
    refine ⟨b, fun x y => ?_⟩
    change b x y = P.cup (rfl : i + j = i + j) x y
    exact (hb x y).trans (cup_eq_local x y).symm
  refine ⟨hb, ?_⟩
  rintro r s x ⟨z, rfl, hz⟩ y ⟨w, rfl, hw⟩
  let F := CH.modF (thA (smFun X q))
  have hc := CrystallineSemistableComparison.Auxff.closed Q (rfl : i + j = i + j) z.1 w.1 z.2 w.2
  have e : P.cup (rfl : i + j = i + j) ((CH.cx F).cls z.1 z.2) ((CH.cx F).cls w.1 w.2) =
      (CH.cx F).cls (P.cupC (rfl : i + j = i + j) z.1 w.1) hc := by
    rw [cup_eq_local]
    exact CrystallineSemistableComparison.P.cxcup_cls Q (rfl : i + j = i + j) z.1 w.1 z.2 w.2 hc
  refine ⟨⟨_, hc⟩, e.symm, fun t => ?_⟩
  exact dividedPowerFiltration_mul _ r s (Ideal.mul_mem_mul
    (term_mem t z.1 hz (CH.front rfl) (CH.front_mono rfl)) (term_mem t w.1 hw (CH.back rfl) (CH.back_mono rfl)))

end GlobalTheory.CompanionTheory.CupdR
