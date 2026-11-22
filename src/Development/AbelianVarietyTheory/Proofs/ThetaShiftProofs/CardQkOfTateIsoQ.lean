module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcPts
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_pre (hL : Out.Laws) (hL2 : Out.Laws2) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (D₀ : Out.DegPre R) (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : (k : F) ≠ 0) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ (2 * (D₀.rank + D₀.P.g)) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL hL2 R D₀ F k hk).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  open ReciprocityTheory.ChartRestriction.G.Out in
  have hc : Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) =
      k ^ D₀.rank * Nat.card {g : GtPtF D₀ F // k • g = 0} := by
    open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR in
      let iota : D₀.X →+ GtPtF D₀ F := AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (th D₀ (T := TF (R := R) F) y J) := isCub_cubV D₀.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
      have hi (x : D₀.X) : GtPtF.IsIota x (iota x) := (exists_iota (F := F) hB x).choose_spec
      have he (x : D₀.X) (g : GtPtF D₀ F) : GtPtF.IsIota x g ↔ g = iota x :=
        ⟨fun h => isIota_unique h (hi x), fun h => h ▸ hi x⟩
      let qkMk (y : D₀.X) (g : GtPtF D₀ F) (h : k • g = iota y) : QkPt D₀ F k :=
        ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (he _ _).2 h⟩
      have qk_nsmul (p : QkPt D₀ F k) : k • p.g = iota p.y := by
        obtain ⟨h, h₁, h₂⟩ := p.eq
        exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((he _ _).1 h₂)
      have equiv_iff (p p' : QkPt D₀ F k) : QkPt.Equiv D₀ F p p' ↔ ∃ z : D₀.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota z :=
        exists_congr fun z => and_congr Iff.rfl
          ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((he _ _).1 h₁)),
           fun h => ⟨_, hi z, (isAdd_iff_eq _ _ _).2 h⟩⟩
      have hd : ∀ y : D₀.X, ∃ g : GtPtF D₀ F, k • g = iota y :=
        fun y => exists_nsmul_eq hL.mulN (Or.inl inferInstance) hk0 _
      choose r hr using hd
      let K : AddSubgroup D₀.X := (nsmulAddMonoidHom k : D₀.X →+ D₀.X).range
      have hK : Nat.card (D₀.X ⧸ K) = k ^ D₀.rank := AddSubgroup.index_range_nsmul D₀.X k
      let f : (D₀.X ⧸ K) × {g : GtPtF D₀ F // k • g = 0} → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x =>
        Quot.mk _ (qkMk x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
      rw [← hK, ← Nat.card_prod]
      refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
      · rintro ⟨c, t⟩ ⟨c', t'⟩ h
        obtain ⟨z, hy, hg⟩ := (equiv_iff _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
        change c'.out = c.out + k • z at hy
        change r c'.out + t'.1 = r c.out + t.1 + iota z at hg
        obtain rfl : c = c' := by
          rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
          exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
        have hz : z = 0 := by
          have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
          exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk0)
        rw [hz, map_zero, add_zero, add_right_inj] at hg
        exact Prod.ext rfl (Subtype.ext hg.symm)
      · rintro ⟨p⟩
        obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out ∈ K := by
          rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
        have hy : (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out = p.y + k • z := by
          rw [show k • z = _ from hz, add_neg_cancel_left]
        refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota z - r (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out, ?_⟩,
          (Quot.sound ((equiv_iff _ _).2 ⟨z, hy, ?_⟩)).symm⟩
        · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul, map_add (f := _), map_nsmul, sub_self]
        · exact add_sub_cancel _ _
  rw [hc, h₁, ← pow_add]
  congr 1
  ring

theorem card_qk_of_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hB : D₀.TauBimult) (I : TateIsoQ D D₀ oa F) (k : ℕ) (hk : 0 < k) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ Module.finrank ℤ D.La := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have := datum_free_int D
  let K : AddSubgroup D.La := (nsmulAddMonoidHom k : D.La →+ D.La).range
  have hK : Nat.card (D.La ⧸ K) = k ^ Module.finrank ℤ D.La := AddSubgroup.index_range_nsmul D.La k
  have hE := equiv_equivalence (D := D₀) (F := F) (k := k) hB
  let f : D.La ⧸ K → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x => Quot.mk _ (I.ev k x.out)
  rw [← hK]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x x' h
    obtain ⟨e, he⟩ := (I.ker k hk _ _).1 (hE.symm (hE.eqvGen_iff.1 (Quot.eqvGen_exact h)))
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x', QuotientAddGroup.eq]
    exact ⟨e, by rw [he, neg_add_cancel_left]; rfl⟩
  · rintro ⟨p⟩
    obtain ⟨v, hv⟩ := I.onto k hk p
    obtain ⟨e, he⟩ : -v + (QuotientAddGroup.mk v : D.La ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    refine ⟨QuotientAddGroup.mk v, Quot.sound (hE.trans ((I.ker k hk _ _).2 ⟨e, ?_⟩) hv)⟩
    rw [show k • e = _ from he, add_neg_cancel_left]

theorem finrank_V_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → Module.finrank ℂ Λ.A.V = g := by
  intro hL hL2 E _ _ _ H _ D l c O _ β _ _ b a Λ g ty hty ⟨r, z, hr, hz⟩
  obtain ⟨-, I, -⟩ := a.geom ℂ r z hr hz _ rfl
  have h₁ := card_qk_pre hL hL2 a.D₀ a.bimult ℂ 2 (by norm_num)
  rw [card_qk_of_tateIsoQ a.bimult I 2 two_pos, datum_finrank_int,
    ← (GlobalTheory.PeriodExists.period_of_isTypeFn H D g ty hty).1] at h₁
  have h₂ := Nat.pow_right_injective le_rfl h₁
  have h₃ : Module.finrank ℤ Λ.A.X = a.D₀.rank := (Λ.ε.toAddEquiv.toIntLinearEquiv).finrank_eq
  rw [Λ.A.finrank_V, h₃, Λ.gB_eq]
  omega

end GlobalTheory.ArcPts
end
