module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.InfVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.OpenLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExistsOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoCopy
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoTypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem thinOut {α β : Type} [DecidableEq α] (f : α → β) (S T : Finset α) (hinj : Set.InjOn f (S : Set α)) :
    ∃ T' : Finset α, S ⊆ T' ∧ Set.InjOn f (T' : Set α) ∧ (∀ t ∈ T', t ∉ S → ∀ s ∈ S, f s ≠ f t) ∧
      ∀ t ∈ T, ∃ t' ∈ T', f t' = f t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hinj, fun t h h' => absurd h h', by simp⟩
  | insert a T₀ _ ih =>
    obtain ⟨T', h1, h2, h3, h4⟩ := ih
    by_cases h : ∃ t' ∈ T', f t' = f a
    · refine ⟨T', h1, h2, h3, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact h
      · exact h4 t ht
    · push Not at h
      refine ⟨insert a T', h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h₁ | h₁ <;>
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h₂ | h₂
        · rw [h₁, h₂]
        · subst h₁
          exact absurd hxy.symm (h y h₂)
        · subst h₂
          exact absurd hxy (h x h₁)
        · exact h2 h₁ h₂ hxy
      · intro t ht htS s hs
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact h s (h1 hs)
        · exact h3 t ht htS s hs
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨_, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨t', a', b⟩ := h4 t ht
          exact ⟨t', Finset.mem_insert_of_mem a', b⟩

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem away_congr {n : ℕ} {w w' : Plc L} (h : w.under (𝓞 (Lp L)) = w'.under (𝓞 (Lp L))) :
    away n w = away n w' := by
  simp only [away, h]

private theorem cLoc_away {n : ℕ} {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl

private noncomputable def AT (S : Finset (Plc L)) (W : ∀ w : Plc L, Sig.Lev (Kw w)) (T : Finset (Plc L)) : Subgroup (UA L 2) :=
  lev (Kall (L := L) 2) S W ⊓ ⨅ w ∈ T, away 2 w

open GlobalTheory.SplitPts in
private theorem step [DecidableEq (Plc L)] {V : Type} [AddCommGroup V] [Module ℂ V] (S T₀ : Finset (Plc L))
    (W : ∀ w : Plc L, Sig.Lev (Kw w)) (w : Plc L)
    (hS : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (hT : ∀ t ∈ T₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ φ' : UA L 2 → V)
    (hspan : InSpan w φ φ') (hAF : IsAF R (AT S W (insert w T₀)) φ)
    (hinv : ∀ x ∈ locU 2 w, x ∈ Kall (L := L) 2 → (w ∈ S → cLoc w x ∈ (W w).J 2) → ∀ g, φ' (g * x) = φ' g) :
    IsAF R (AT S W T₀) φ' := by
  have h1 : AT S W (insert w T₀) ≤ away 2 w :=
    inf_le_right.trans (iInf₂_le w (Finset.mem_insert_self _ _))
  have h2 := (spanKeep L 2 V w φ φ' hspan).2.1 R _ h1 hAF
  have hLocAway (v t : Plc L) (h : v.under (𝓞 (Lp L)) ≠ t.under (𝓞 (Lp L))) :
      locU 2 v ≤ away 2 t := by
    intro x hx
    refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
      (by rw [hu]; exact h.symm)
  have hSplit (g : UA L 2) : ∃ x ∈ locU 2 w, ∃ y ∈ away 2 w, g = x * y := by
    classical
    let P (u : Plc L) := u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    let e : Af L :=
      ⟨fun u => if P u then 1 else 0, Filter.Eventually.of_forall fun u => by
        dsimp only
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩
    let cut (A : Matrix (Fin 2) (Fin 2) (Af L)) := e • A + (1 - e) • 1
    have hpos (A : Matrix (Fin 2) (Fin 2) (Af L)) (u : Plc L) (hu : P u) :
        RingHom.mapMatrix (pLoc L u) (cut A) = RingHom.mapMatrix (pLoc L u) A := by
      have he : pLoc L u e = 1 := ite_eq_left hu
      ext i j
      simp [cut, Matrix.add_apply, Matrix.smul_apply, he]
    have hneg (A : Matrix (Fin 2) (Fin 2) (Af L)) (u : Plc L) (hu : ¬ P u) :
        RingHom.mapMatrix (pLoc L u) (cut A) = 1 := by
      have he : pLoc L u e = 0 := ite_eq_right hu
      refine Matrix.ext fun i j => ?_
      change pLoc L u (e * A i j + (1 - e) * (1 : Matrix (Fin 2) (Fin 2) (Af L)) i j) =
        (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion L)) i j
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, he, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hmul {A B : Matrix (Fin 2) (Fin 2) (Af L)} (h : A * B = 1) :
        cut A * cut B = 1 := by
      refine matAf_ext fun u => ?_
      rw [map_mul, map_one]
      by_cases hu : P u
      · rw [hpos _ _ hu, hpos _ _ hu, ← map_mul, h, map_one]
      · rw [hneg _ _ hu, hneg _ _ hu, one_mul]
    let a := Matrix.GeneralLinearGroup.map (pFin L) g.1
    let k : GL (Fin 2) (Af L) :=
      ⟨cut a.val, cut (a⁻¹).val, hmul (by simp), hmul (by simp)⟩
    have hcomp (u : Plc L) (hu : P u) :
        Matrix.GeneralLinearGroup.map (pLoc L u) k = cLoc u g :=
      Units.ext (hpos _ _ hu)
    have hzero (u : Plc L) (hu : ¬ P u) :
        Matrix.GeneralLinearGroup.map (pLoc L u) k = 1 :=
      Units.ext (hneg _ _ hu)
    have hmem : finGL L 2 k ∈ UA L 2 := by
      refine finGL_mem_UA k fun u => ?_
      have hconj : (conjSrc (conjE L) u).under (𝓞 (Lp L)) = u.under (𝓞 (Lp L)) :=
        (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
          (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) u _).2
          (Or.inr (conjPl_self_conjSrc u))
      by_cases hu : P u
      · rw [hcomp u hu, hcomp _ (hconj.trans hu)]
        exact comp_eq g u
      · rw [hzero u hu, hzero _ (fun h => hu (hconj.symm.trans h))]
        simp
    let x : UA L 2 := ⟨_, hmem⟩
    have hloc (u : Plc L) : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) k := by
      change Matrix.GeneralLinearGroup.map ((pLoc L u).comp (pFin L)) (finGL L 2 k) = _
      exact Units.ext (congrArg (fun M : GL (Fin 2) (Af L) => RingHom.mapMatrix (pLoc L u) M.val) (pFin_finGL k))
    refine ⟨x, Subgroup.mem_inf.2 ⟨pInf_finGL k, ?_⟩, x⁻¹ * g, ?_, by group⟩
    · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_
      exact MonoidHom.mem_ker.2 ((hloc u).trans (hzero u hu))
    · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_
      rw [map_mul, map_inv, hloc u, hcomp u hu, inv_mul_cancel]
  have hIntegral {x y : UA L 2} (hx : x ∈ locU 2 w) (hy : y ∈ away 2 w)
      (hxy : x * y ∈ Kall (L := L) 2) :
      x ∈ Kall (L := L) 2 ∧ y ∈ Kall (L := L) 2 := by
    have hxinf : cInf x = 1 := (Subgroup.mem_inf.1 hx).1
    have hyinf : cInf (x * y) = 1 := (Subgroup.mem_inf.1 hxy).1
    rw [map_mul, hxinf, one_mul] at hyinf
    have hLoc (u : Plc L) :
        cLoc u x ∈ GlobalTheory.LFun.KGL u (n := 2) ∧
        cLoc u y ∈ GlobalTheory.LFun.KGL u (n := 2) := by
      have huK := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxy).2 u)
      by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · have hyu : cLoc u y = 1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu
        rw [map_mul, hyu, mul_one] at huK
        exact ⟨huK, hyu.symm ▸ one_mem _⟩
      · have hxu : cLoc u x = 1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu
        rw [map_mul, hxu, one_mul] at huK
        exact ⟨hxu.symm ▸ one_mem _, huK⟩
    exact ⟨Subgroup.mem_inf.2 ⟨hxinf, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (hLoc u).1⟩,
      Subgroup.mem_inf.2 ⟨hyinf, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (hLoc u).2⟩⟩
  refine ⟨h2.left, h2.inf, ?_⟩
  intro u hu g
  obtain ⟨x, hx, y, hy, rfl⟩ := hSplit u
  obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hK, hJ⟩ := Subgroup.mem_inf.1 hlev
  have hxy := hIntegral hx hy hK
  have hJ' : ∀ v ∈ S, cLoc v (x * y) ∈ (W v).J 2 := fun v hv =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hJ v) hv
  have hyw : cLoc w y = 1 := cLoc_away hy
  have hyA : y ∈ AT S W (insert w T₀) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxy.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
      show cLoc v y ∈ (W v).J 2
      by_cases hvw : v = w
      · subst hvw
        rw [hyw]
        exact one_mem _
      · have hxv : cLoc v x = 1 :=
          cLoc_away (hLocAway w v (hS v hv hvw).symm hx)
        have := hJ' v hv
        rwa [map_mul, hxv, one_mul] at this
    · refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hy
      · have hxt : x ∈ away 2 t := hLocAway w t (hT t ht).symm hx
        have hxyt : x * y ∈ away 2 t := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t) ht
        exact (Subgroup.mul_mem_cancel_left _ hxt).1 hxyt
  rw [← mul_assoc, h2.level y hyA, hinv x hx hxy.1 ?_]
  intro hwS
  have := hJ' w hwS
  rwa [map_mul, hyw, mul_one] at this

end
