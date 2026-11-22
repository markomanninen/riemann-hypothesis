module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HatInt in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by
    have := l₂.three_le
    omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    let single : Fin (Vc D i).rank → Dw.La := Pi.single b w
    let shift : Fin (Vc D i).rank → Dw.La := fun j => H.bar s • single j
    have hinv : ∀ x, φ (x + fun j => Submodule.Quotient.mk (shift j)) = φ x := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y : Fin (Vc D i).rank → Dw.La,
          x = fun j => Submodule.Quotient.mk (y j) :=
        ⟨fun j => qRep (x j), funext fun j =>
          (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x j))).symm⟩
      have hshift := (he (fun j => y j + shift j)).2
      have horig := (he y).2
      simp only [RingHom.id_apply] at hshift horig
      have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j + shift j)) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j)) := by
        intro PP hP
        have hmap : (fun j => ι (y j + shift j)) =
            fun j => ι (y j) + ((H.bar s : 𝓞 D.host.E) : D.host.E) • ι (single j) := by
          funext j
          change ι (y j + H.bar s • single j) = _
          rw [map_add (f := _), map_smul]
          rfl
        rw [hmap, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he y).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => hred PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => hred PP (Or.inr hP)), ← horig] at hshift
      change φ (fun j => Submodule.Quotient.mk (y j) + Submodule.Quotient.mk (shift j)) = _
      simpa only [Submodule.Quotient.mk_add] using hshift
    have hpair := dvd_of_invariant l₂ φ q hq shift hinv
    unfold Formalism.L2.Pj.pairL at hpair
    rw [Finset.sum_eq_single b] at hpair
    · simpa [shift, single, Dw.adj, LevelPairing.bar_bar] using hpair
    · intro j _ hj
      simp [shift, single, Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have halt := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at halt
    have hskew : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by
      linarith
    rw [hskew]
    exact (hdvd y).neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩
