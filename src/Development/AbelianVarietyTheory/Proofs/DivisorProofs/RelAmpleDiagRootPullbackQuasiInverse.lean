module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePullOfIsFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.CechPic

theorem relAmple_diag_root_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro p _ D R _ b N c Y _ s o B _ _ ψ ψ' hp hc hB hq P' hP' hiso _
  obtain ⟨e, rfl⟩ := hc
  have hu : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [Nat.cast_pow]
    exact h.pow e
  have hq' : IsQuasiInv (p ^ e) ψ' ψ := ⟨hq.2.1, hq.1, hq.2.2.2, hq.2.2.1⟩
  have hfin := (isFinite_etale_surjective_of_isQuasiInv Y B o.A (p ^ e) ψ' ψ hB o.ab hu hq').1
  have := hB.proper
  have := o.ab.proper
  have hL := hP'.1
  have hD := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have a₁ := GlobalTheory.RootDiagAmple.relAmple_pull_of_isFinite ψ' hD o.ample
  have relAmple_of_pow {A : Over Y} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
      (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (eq : cls M hM = d • cls L hL)
      (h : Out.RelAmple A M) : Out.RelAmple A L := by
    rw [relAmple_iff_isAmpleLB A hM] at h
    refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
    refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
      ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
    rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, eq, map_nsmul]
  refine relAmple_of_pow (pull_isLB hL _) (pull_isLB hD _)
    (d := p ^ e) (Nat.one_le_pow e p ((Fact.out : p.Prime).pos)) ?_ a₁
  have hpow : (Hecke.lbPow P' (p ^ e)).IsLB := LB.isLB_linComb hL _ _
  have ec := (cls_eq_iff (pull_isLB o.isLB _) hpow).2 hiso
  have ep : cls _ hpow = (p ^ e) • cls P' hL := by
    refine (cls_linComb hL (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1) hpow).trans ?_
    simp [pull_id]
  rw [cls_pull hL, cls_pull hD, cls_pull o.isLB, ← pull_comp]
  have m : ψ'.left ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 B) (𝟙 B)).left ≫ Hecke.sq2 ψ' := by
    rw [Hecke.sq2, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [m, pull_comp, ← cls_pull o.isLB _ (pull_isLB o.isLB _), ec, ep, map_nsmul]

end GlobalTheory.UPel.HT.ES
