module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.LastSeeSawDatum (comb_apply' comb_smul_fun comb_sum_fun comb_swap vac_smul vac_sum) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatum_exists_at_levelPrimePlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hIC n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum D k p q ψ hψ hU χ hχ hIC n n' n'' V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LA LS LT LX hLA hLS hLT hLX hβQ hγΛ c c' hc hc' hcv hcv'
  obtain ⟨e, he, heP⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p n n' ψ hψ hU A S α β LA LS hLA hLS Ψ c hc hcv
  obtain ⟨e', he', heP'⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p (n'' ⊕ Fin 1) n ψ hψ hU S X β γ₀ LS LX hLS hLX _ c' hc' hcv'
  refine ⟨e, e', he, he', ?_⟩
  intro L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂
  have ha : charInd (resChar χ hχ q) Q ≠ 0 := by
    intro h
    have hev : Q.ev 0 = 0 := by
      unfold Pair.ev
      rw [dite_eq_left Q.lat.zero_mem]
      exact map_zero Q.fn
    have h0 := congrFun h 0
    simp only [charInd, vecInd, hev, neg_zero, AddChar.map_zero_eq_one, Q.lat.zero_mem, ite_true, mul_one,
      Pi.zero_apply] at h0
    exact one_ne_zero h0
  have hA : ∀ y : WO L S, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) ∧
      comb ψ A S c (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) = fun u => Ξ ((o.resS S).symm (u, y)) := by
    intro y
    obtain ⟨g, hg⟩ := GlobalTheory.T.sliceAlongLine_datum_over_vacuum_splitPlace D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ _ ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
    exact heP g _ hg
  have hcol : ∀ x, (fun u => lastBi o o'' τ Ξ Φ₂ u x) =
      Φ₂ (o''.resT S x).1 • fun u => Ξ ((o.resS S).symm (u, kap τ S (o''.resT S x).2)) := by
    intro x; funext u; rfl
  have hAc : ∀ x, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) ∧
      comb ψ A S c (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) = fun u => lastBi o o'' τ Ξ Φ₂ u x := by
    intro x
    rw [hcol x, comb_smul_fun, comb_smul_fun]
    exact ⟨vac_smul _ (hA _).1, by rw [(hA _).2]⟩
  have hX : ∀ u, Vac ψ S X LS LX (· = p.v) (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) ∧
      comb ψ S X c' (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) = lastBi o o'' τ Ξ Φ₂ u := by
    intro u
    obtain ⟨g, hg⟩ := hε α α₀ β γ γ₀ hα hγ Q Λ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
    exact heP' g _ hg
  generalize lastBi o o'' τ Ξ Φ₂ = C at hAc hX ⊢
  refine ⟨⟨fun x => ?_, fun u => ?_⟩, ?_⟩
  · have e1 : (fun u' => comb ψ S X e' (C u') x) =
        ∑ j ∈ e'.support, (e' j * ψ (symplOH S X x j)) • fun u' => C u' (x + j) := by
      funext u'
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u' => comb ψ S X e' (C u') x))
    rw [e1, comb_sum_fun]
    exact vac_sum _ _ _ fun j _ => (hAc (x + j)).1
  · have e2 : (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u) =
        ∑ i ∈ e.support, (e i * ψ (symplOH A S u i)) • comb ψ S X e' (C (u + i)) := by
      funext x
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ S X LS LX (· = p.v) (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u)
    rw [e2]
    exact vac_sum _ _ _ fun i _ => (hX (u + i)).1
  · funext u x
    have hsw : ∀ u', comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x =
        comb ψ A S e (fun u'' => C u'' x) u' := by
      intro u'
      have h1 := comb_swap (ψ := ψ) e c' (fun u'' x' => comb ψ S X e' (C u'') x') u' x
      beta_reduce at h1
      rw [h1]
      congr 1
      funext u''
      exact congrFun (hX u'').2 x
    show C u x = comb ψ A S c (fun u' => comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x) u
    simp only [hsw]
    exact (congrFun (hAc x).2 u).symm
