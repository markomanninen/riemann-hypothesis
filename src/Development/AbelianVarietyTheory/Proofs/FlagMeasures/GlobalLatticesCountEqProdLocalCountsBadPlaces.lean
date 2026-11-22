module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChangeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpanStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermNoDefectPrimeToInvariantsStatement

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Fibre

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem finrank_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp, rank_eq]

theorem theta_eq_one {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {p : PlF D}
    (h : (FP p).PrimeTo) : LocNG.theta (Z.M p) = 1 := by
  unfold LocNG.theta
  rw [h.1]

theorem isLat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ := GlobalTheory.T.localTermLattice_over_innerDatum_fg_span

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := GlobalTheory.T.localTerm_noDefect_primeTo_invariants

theorem full_of_local_span {D : D7} (Z : LocDat D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) (p : PlF D)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let A := GlobalTheory.HL.placesOf Z
  have hcoord : Submodule.span D.host.E (LatLoc.cL Λ : Set (Fin (nV D) → D.host.E)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hzero⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have := (A.loc p).lf
    have := (A.loc p).char0
    have := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
    let ψ : (Fin (nV D) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
      ∑ i : Fin (nV D), (A.loc p).ιE (φ fun j => if i = j then 1 else 0) • LinearMap.proj i
    have hψ (z : Fin (nV D) → D.host.E) : ψ (A.bc p z) = (A.loc p).ιE (φ z) := by
      rw [φ.pi_apply_eq_sum_univ z, map_sum]
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, map_mul, GlobalTheory.HL.Places.bc]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hlat : A.lat p (LatLoc.cL Λ) ≤ (LinearMap.ker ψ).restrictScalars (A.L p).O := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      have hz' : φ z ∈ (⊥ : Submodule D.host.E D.host.E) := by
        rw [← hzero]
        exact Submodule.mem_map_of_mem (Submodule.subset_span hz)
      change ψ (A.bc p z) = 0
      rw [hψ, (Submodule.mem_bot D.host.E).mp hz', map_zero]
    have hker : Submodule.span (A.loc p).Ep (A.lat p (LatLoc.cL Λ) : Set _) ≤ LinearMap.ker ψ :=
      Submodule.span_le.mpr hlat
    rw [LatLoc.localLattice_eq] at hspan
    change Submodule.span (A.loc p).Ep (A.lat p (LatLoc.cL Λ) : Set (Fin (nV D) → (A.loc p).Ep)) = ⊤ at hspan
    rw [hspan] at hker
    apply hφ
    apply LinearMap.ext
    intro z
    have hz := LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := A.bc p z)))
    rw [hψ] at hz
    exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp hz
  refine { toIsLattice := hΛ, span_eq_top := ?_ }
  have hm : (Submodule.span D.host.E (Λ : Set (VS D).V)).map (LatLoc.cE D).toLinearMap = ⊤ := by
    rw [← Submodule.span_image]
    exact hcoord
  apply eq_top_iff.mpr
  intro x _
  have hx : LatLoc.cE D x ∈ (Submodule.span D.host.E (Λ : Set (VS D).V)).map (LatLoc.cE D).toLinearMap := by
    rw [hm]
    exact Submodule.mem_top
  obtain ⟨y, hy, heq⟩ := hx
  have : y = x := (LatLoc.cE D).injective heq
  simpa [this] using hy

theorem fibre : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ y : Dat Z FP, (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) → {p | y p ≠ d0 p}.Finite → ((globSet G G' y).encard : ℝ≥0∞) = ∏ p ∈ P, ((locSet G G' p (y p)).encard : ℝ≥0∞) := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS y hrel hfin
  obtain ⟨hBased, hRelG, hPrime, hTerm0, Λ₀, hΛ₀, hΛ₀t⟩ := hB
  obtain ⟨-, -, -, -, hloc⟩ := hS
  have hLG := LatLoc.lattices_local_global D Z
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p₀, hp₀⟩ : ∃ p : PlF D, p ∉ P := by
    by_contra h
    push_neg at h
    exact Set.infinite_univ (α := PlF D) (P.finite_toSet.subset fun p _ => h p)
  have hΛ₀full : Submodule.IsFullLattice D.host.E Λ₀ :=
    full_of_local_span Z Λ₀ hΛ₀ p₀ (isLat D Z FP p₀ (d0 p₀) _ (hΛ₀t p₀ hp₀)).2

  have single : ∀ p, p ∉ P → ∃! L, L ∈ locSet G G' p (y p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have key := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_eq p)
      (hRelG p) (hPrime p hp) A A' (fun a b h => ⟨hA.1 a b h, hA'.1 a b h⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
      (scaled Z p (frame G)) (scaled Z p (frame G'))
      (fun j => by rw [hc j, (hBased p).1]; rfl) (fun j => by rw [hc' j, (hBased p).2.1]; rfl)
      (d0 p) (hTerm0 p) (y p)
    exact key.1 (hrel p hp)

  have std : ∀ p, p ∉ P → y p = d0 p → lattice₂ D Z.M p Λ₀ ∈ locSet G G' p (y p) := by
    intro p hp hy
    rw [hy]
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have hT : LocNG.IsTermOver (FP p) (d0 p) (tm FP G G' p (lattice₂ D Z.M p Λ₀)) :=
      GlobalTheory.T.hermitian_frame_witness_integral_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_eq p) (hRelG p) (d0 p)
        (tm FP F F' p (lattice₂ D Z.M p Λ₀)) (hΛ₀t p hp) A A' (scaled Z p (frame G)) (scaled Z p (frame G')) hA hA'
        (fun a b => ⟨(hint a b).1, (hint a b).2, by
          rw [theta_eq_one (hPrime p hp), map_one]
          refine Submodule.mem_span_singleton.2 ⟨⟨A a b - A' a b, (Z.M p).L.O.sub_mem (hint a b).1 (hint a b).2⟩, ?_⟩
          first
            | (rw [Algebra.smul_def, mul_one]; rfl)
            | (rw [Submodule.smul_def]; simp)
            | (simp [Algebra.smul_def])
            | (erw [smul_eq_mul, mul_one])
            | (change (A a b - A' a b) * 1 = _; rw [mul_one])⟩) hc hc'
    exact ⟨hT, noDefect D Z FP p (hRelG p) (hPrime p hp) (d0 p) _ hT⟩

  let Φ : LV D → ∀ q : P, Submodule (Z.M q).L.O (Vp D q) := fun Λ q => lattice₂ D Z.M q Λ
  have hinj : Set.InjOn Φ (globSet G G' y) := by
    intro Λ₁ h₁ Λ₂ h₂ e
    refine (hLG.1 Λ₁ Λ₂ (full_of_local_span Z Λ₁ h₁.1 p₀ (isLat D Z FP p₀ (y p₀) _ (h₁.2 p₀).1).2) (full_of_local_span Z Λ₂ h₂.1 p₀ (isLat D Z FP p₀ (y p₀) _ (h₂.2 p₀).1).2)).2 fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun e ⟨p, hp⟩
    · exact (single p hp).unique (h₁.2 p) (h₂.2 p)
  have himg : Φ '' globSet G G' y = Set.univ.pi (fun q : P => locSet G G' q (y q)) := by
    ext g
    constructor
    · rintro ⟨Λ, hΛ, rfl⟩ q -
      exact hΛ.2 q
    · intro hg
      let Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p) := fun p =>
        if h : p ∈ P then g ⟨p, h⟩ else (single p h).exists.choose
      have hLp : ∀ p, Lp p ∈ locSet G G' p (y p) := by
        intro p
        by_cases h : p ∈ P
        · simp only [Lp, dif_pos h]; exact hg ⟨p, h⟩ (Set.mem_univ _)
        · simp only [Lp, dif_neg h]; exact (single p h).exists.choose_spec
      have hlat : ∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤ :=
        fun p => isLat D Z FP p (y p) (tm FP G G' p (Lp p)) (hLp p).1
      have hfin' : {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite := by
        refine ((P.finite_toSet).union hfin).subset fun p hp => ?_
        by_contra hn
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hn
        exact hp ((single p hn.1).unique (hLp p) (std p hn.1 hn.2))
      obtain ⟨Λ, hΛ, hΛp⟩ := hLG.2 Λ₀ hΛ₀full Lp hlat hfin'
      refine ⟨Λ, ⟨hΛ, fun p => by rw [hΛp p]; exact hLp p⟩, ?_⟩
      funext q
      show lattice₂ D Z.M q Λ = g q
      rw [hΛp q]
      show (if h : (q : PlF D) ∈ P then g ⟨q, h⟩ else (single q h).exists.choose) = g q
      rw [dif_pos q.2]
  have e1 := hinj.encard_image
  rw [himg, Set.encard_pi_eq_prod_encard] at e1
  rw [← e1]
  exact (map_prod ENat.toENNRealRingHom (fun i : P => (locSet G G' i (y i)).encard) Finset.univ).trans
    (Finset.prod_coe_sort P (fun p => ((locSet G G' p (y p)).encard : ℝ≥0∞)))

end GlobalTheory.GenMass.Fibre
