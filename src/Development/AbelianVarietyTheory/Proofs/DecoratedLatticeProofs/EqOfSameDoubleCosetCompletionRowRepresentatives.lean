module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRationStatement

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge.RepsInj

open GlobalTheory.TwBridge.Lev (dc_iff mem_par_iff phi)

theorem reps_injOn : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s), Set.InjOn (DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J ) {g : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g} := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _hν _hc hA L G _hL hI j c h
  have sameDC (i d : ℕ) (hd : i + d = s + 1) (γ γ' : AutY X R i)
      (g g' : GL (XIx (Fin R.k) (Fin R.t) i ⊕ Fin d) k) (hg : IsGL ι γ g) (hg' : IsGL ι γ' g')
      (hmk : DoubleCoset.mk (GlobalTheory.RootEx.R k _ d 1) ((W.T s R).lev i d hd).J g =
        DoubleCoset.mk (GlobalTheory.RootEx.R k _ d 1) ((W.T s R).lev i d hd).J g') :
      SameDC (Pr := Pr) cst.sharp i P.1 γ γ' := by
    have hc : d = cOf R i := by
      have := hA.steps
      unfold cOf
      omega
    subst d
    obtain ⟨e, he, hg⟩ := hg
    obtain ⟨e', he', hg'⟩ := hg'
    have heq : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
    subst e'
    obtain rfl : g = phi ι e γ := Units.ext hg
    obtain rfl : g' = phi ι e γ' := Units.ext hg'
    let o := stdOrd (Fin R.k) (Fin R.t) i (cOf R i) hd
    have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := by
      intro g
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply,
        show (plainFrame (k := k) o).bas = 1 from rfl,
        show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
      simp
    have hJ : ∀ g, g ∈ ((W.T s R).lev i (cOf R i) hd).J ↔
        (reGL o).symm g ∈ (parahoric _ (Fin i × Fin R.t) W.δ W.tame).J := by
      intro g
      rw [← hconj]
      rfl
    have hmem : ∀ γ : AutY X R i, phi ι e γ ∈ ((W.T s R).lev i (cOf R i) hd).J ↔
        γ ∈ Jat (Pr := Pr) cst.sharp i P.1 := by
      intro γ
      rw [hJ, Jat, ite_eq_right hA.nmem]
      exact mem_par_iff hA.compl W.unif hd rfl he W.tame γ
    exact (dc_iff ι hA.compl.dense (fun a => GlobalTheory.SymBridge.Coords.xPos_lt a) he _
      (fun u hu => (hJ u).2 (((parahoric _ (Fin i × Fin R.t) W.δ W.tame).reindex o).KOne_le hu))
      _ hmem γ γ').2 hmk
  rintro g₁ ⟨b, hb⟩ g₂ ⟨b', hb'⟩ hmk
  have hS := sameDC (j + 1) (c + 1) (by omega) _ _ g₁ g₂ hb hb' hmk
  have heq : L.h (j + 1) b P = L.h (j + 1) b' P := hI (j + 1) b b' P hS
  rw [← heq] at hb'
  obtain ⟨e₁, he₁, h₁⟩ := hb
  obtain ⟨e₂, he₂, h₂⟩ := hb'
  have he : e₁ = e₂ := by
    ext a
    exact (he₁ a).trans (he₂ a).symm
  subst he
  exact Units.ext (h₁.trans h₂.symm)

end GlobalTheory.TwBridge.RepsInj
