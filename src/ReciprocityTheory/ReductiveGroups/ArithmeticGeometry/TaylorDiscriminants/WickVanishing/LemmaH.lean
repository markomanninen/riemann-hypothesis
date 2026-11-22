module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCWick

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

abbrev kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k) (l l' : ι) : k :=
  if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0

theorem kapW_eq_kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) :
    kapW m s (fun l => (u l, 0)) (fun l => (0, φ l)) = kapH m c s u φ := by
  funext l l'
  show (if s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0) =
    (if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0)
  by_cases hs : s l = true ∧ s l' = false
  · rw [if_pos hs]
    by_cases hc : c l = c l'
    · rw [if_pos ⟨hc, hs⟩]
    · rw [if_neg (fun h => hc h.1), hFU l l' (fun h => hc h.1), mul_zero]
  · rw [if_neg hs, if_neg (fun h => hs h.2)]

theorem rename_qsmul {ι τ : Type} (e : ι → τ) (q : ℚ) (X : MvPolynomial ι k) :
    MvPolynomial.rename e (q • X) = q • MvPolynomial.rename e X := by
  exact map_rat_smul (MvPolynomial.rename e) q X

theorem ordNabla_expand (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι π : Type}
    [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        nablaPoly k B h m u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) (liftX k g) := by
  classical
  have hb0 : ∀ l, ((fun l => ((0 : Fin d → k), φ l)) l).1 = 0 := fun l => rfl
  have haa : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (u l', 0) = 0 := by
    intro l l' _
    simp [betaH]
  have hab : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (0, φ l') = 0 :=
    fun l l' hs => hUF l l' (fun h => h.2 hs)
  have ordNabla_wick (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
      [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
      (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
      (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
      ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
        ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
          PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
            (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
            (liftX k f) := by
    have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
      rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
      exact betaH_zero_zero _ _
    have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
      rw [betaH_antisymm, hab l' l e.symm, neg_zero]
    have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
    have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
    have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
    have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
    have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
        nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
      nablaL_add B h m _ _ _ _
    have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
        (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
      rw [hsum, hsum]
      exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
    rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
    have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
    have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
    have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
      (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
      (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
        cB _ _⟩)
      (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
        cB _ _⟩)
      (fun i j => cB _ _)
      (fun i j => by
        rw [nablaL_bracket hN2 B h m]
        unfold kapE kapW
        rw [if_pos ⟨side_inl s i, side_inr s j⟩])
      (fun i => by
        rw [Module.End.smul_def, opL, hb0]
        exact hN3 R d O k B h m _ f)
      (fun j => by
        rw [Module.End.smul_def, opR, hb0]
        exact hN3 R d O k B h m _ f)
      (MvPolynomial.rename (sideE s) P)
    rw [hL, hR, ← Module.End.smul_def, key]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]
  have ordNabla_u (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
      (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
      ordNabla k B h m s (fun l => (u l, 0)) P G = nablaPoly k B h m u P G := by
    have hcomm : ∀ a b : ι, Function.Commute (nabla k B h m (u a) 0) (nabla k B h m (u b) 0) := by
      intro a b z
      have hz := hN2 R d O k B h m (u a, 0) (u b, 0) z
      have hb : betaH k (u a, (0 : Fin d → k)) (u b, 0) = 0 := by simp [betaH]
      rw [hb, mul_zero, map_zero, zero_mul] at hz
      exact sub_eq_zero.mp hz
    unfold ordNabla nablaPoly
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [← List.foldr_append]
    refine List.Perm.foldr_eq' (List.filter_append_perm _ _) ?_ _
    intro x _ y _ z
    exact (hcomm y x).iterate_iterate (n y) (n x) z
  have hw := ordNabla_wick hN2 hN3 B h m s (fun l => (u l, 0)) (fun l => (0, φ l)) hb0 haa hab Q g
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hw
  have hdeg : (MvPolynomial.rename (sideE s) Q).totalDegree = Q.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv (R := k) (sideE s) Q
  rw [hw, kapW_eq_kapH m c s u φ hFU, hdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rename_qsmul, ← ordNabla_eq B h m s (fun l => (u l, 0)) ?_, ordNabla_u hN2]
  intro l l' _
  exact nablaL_comm hN2 B h m _ _ (by simp [betaH])

theorem ordNabla_value_expand (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d)
    (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι π : Type} [Fintype ι] [DecidableEq π] (c : ι → π)
    (s : ι → Bool) (u φ : ι → Fin d → k) (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    constantCoeff (ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g)) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        constantCoeff (DpolyOf (B.FK k) u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ordNabla_expand hN2 hN3 B h m c s u φ hUF hFU Q g, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact hV R d O k B h hax m ι u _ g

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
