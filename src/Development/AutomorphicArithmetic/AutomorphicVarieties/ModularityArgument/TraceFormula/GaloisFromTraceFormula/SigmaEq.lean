module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OneSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CsdSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.CuspFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem sigma_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a n : ℕ} (e : a = n) (Q : CuspSub E a)
    (π : CuspSub E n) (h : e ▸ Q.V = π.V) : (⟨a, CG.mk Q⟩ : Σ k, CG E k) = ⟨n, CG.mk π⟩ := by
  subst e
  have : Q = π := CuspSub.ext h
  rw [this]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.preOf :
    PartNorm → GOne.CsdSat → Places → PreOf := by
  intro hN hC hPl E _ _ _ n hn π hd D hHas hReg hIn hSp
  have hcc := fun w : Pl E => ((hPl E).2.1 w).1
  have hsp := fun w : Pl E => ((hPl E).2.1 w).2
  choose P hP hnorm hunit using hN E n hn π hd D hReg hSp
  have hl : ∀ i w, ∃ σ, IsLocCompGL (P i).V w σ := fun i w =>
    (GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E (D.N i) (P i) w).imp fun σ h =>
      ((cuspSub_iff (P i)).2.1 w σ).2 h.1
  choose σ hσ using hl
  have hdisc (i : Fin D.c) : IsDiscrete (P i).V :=
    isDiscrete_of_cuspSub (P i) fun φ hφ => by
      obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant
        ((P i).cusp φ hφ) (hnorm i φ hφ)
      exact GlobalTheory.DiscChar.isSqInt_of_bounded (hnorm i φ hφ) (C := C) fun g => by
        simpa using hC g
  have hinf (i : Fin D.c) (τ : E →+* ℂ) :
      HasInfCharGL (P i).V τ ((CG.mk (P i)).infChar τ) :=
    ((cuspSub_iff (P i)).2.2 τ _).2 (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk (P i)) τ)
  let D' : PositivityTheory.Rg.BcB.F.Pre E n := ⟨D.c, D.N, D.sum, fun i => (P i).V, σ, fun i τ => (CG.mk (P i)).infChar τ,
    D.pos, hdisc, hσ, hinf⟩
  have hsat : ∀ w B, D.Sat w B → D'.Sat w B := by
    rintro w B ⟨b, hb, rfl⟩
    refine ⟨b, fun i => ?_, rfl⟩
    let part : PositivityTheory.Rg.BcB.F.Pre E (D.N i) :=
      ⟨1, fun _ => D.N i, by simp, fun _ => (P i).V, fun _ => σ i,
        fun _ => (CG.mk (P i)).infChar, fun _ => D.pos i, fun _ => hdisc i,
        fun _ => hσ i, fun _ => hinf i⟩
    have hone : GOne.One part (P i) := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
    have hpart := (GOne.oneSat E (D.N i) (D.pos i) (P i) part hone w (b i)).1
      (by rw [hP i]; exact hb i)
    obtain ⟨b', hb', hsum⟩ := hpart
    have heq : b' 0 = b i := by simpa using hsum
    exact heq ▸ hb' 0
  have hconj {w u : Pl E} (h : PositivityTheory.Rg.BcB.F.ConjPl w u) : cPl u = w := by
    obtain ⟨hunder, hsplit⟩ := h
    by_cases e : u = w
    · subst e
      exact (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 (hsplit.resolve_left fun h => h rfl)
    · rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
        (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 hunder.symm with h | h
      · exact absurd h.symm e
      · refine (eq_conjSrc ?_).symm
        rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h ⊢
        intro x y hxy
        refine (h y x ?_).symm
        rw [hxy]
        exact (IsCMField.complexConj_apply_apply E _).symm
  have hcof : Tendsto (cPl : Pl E → Pl E) cofinite cofinite :=
    Function.Injective.tendsto_cofinite fun x y e => by rw [← hcc x, ← hcc y, e]
  refine ⟨D', fun τ => ?_, ?_, hSp.mono fun w hw hs => (hw hs).imp fun B hB => ⟨hsat w B hB.1, hB.2⟩, ?_⟩
  · obtain ⟨lam, hlam⟩ := hReg τ
    refine ⟨lam, ?_⟩
    rw [← hlam]
    exact Finset.sum_congr rfl fun i _ => by simp only [D', hP i]
  · filter_upwards [hIn, hSp, hcof.eventually hSp, hC E n hn π hd] with w h1 h2 h3 h4
    by_cases hw : IsSplitAt w
    · obtain ⟨B, hB, hπ⟩ := h2 hw
      obtain ⟨B', hπ', hu⟩ := h4
      obtain rfl := CG.HasSat.unique hπ hπ'
      refine ⟨B, hsat w B hB, fun u hu' => ?_⟩
      have e : u = cPl w := by rw [← hconj hu', hcc]
      have hs : IsSplitAt u := by
        rw [e]
        refine (hsp _).2 ?_
        rw [hcc]
        exact ((hsp w).1 hw).symm
      obtain ⟨B₂, hB₂, hπ₂⟩ := e ▸ h3 (e ▸ hs)
      obtain rfl := CG.HasSat.unique hπ₂ (hu u hu')
      exact hsat _ _ hB₂
    · obtain ⟨B, hB, hinv⟩ := h1 hw
      refine ⟨B, hsat w B hB, fun u hu' => ?_⟩
      have e : u = w := by
        rw [← hcc u, hconj hu']
        by_contra h
        exact hw ((hsp w).2 h)
      subst e
      have : B.map (·⁻¹) = B := hinv
      rw [this]
      exact hsat _ _ hB
  · rintro ⟨hc, h⟩
    have i : Fin D.c := ⟨0, by have : D.c = 1 := hc; omega⟩
    obtain ⟨e, he⟩ := h i
    refine hHas ⟨i, ?_⟩
    rw [← hP i]
    exact sigma_eq e (P i) π he
