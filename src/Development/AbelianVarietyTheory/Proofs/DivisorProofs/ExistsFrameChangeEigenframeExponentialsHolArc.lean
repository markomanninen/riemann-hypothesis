module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ShFam.BdArc

open GlobalTheory.HolHom GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections LatSec

theorem exists_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), IsArc Z σ φ x ψ r → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ h : ℂ → (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), ∀ u ∈ Metric.ball (0 : ℂ) ρ, (h u).IsInvertible ∧ ContinuousAt (fun u => (h u).inverse) u ∧ ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = e' u (h u z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  have hA : ∀ u ∈ Metric.ball (0 : ℂ) ρ, HolAt (fun z => (e' u z).left) 0 := fun u hu =>
    holAt_of_isHolTo (hexp u hu).2.2.1 trivial
  have hh : ∀ u, ∃ h : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), u ∈ Metric.ball (0 : ℂ) ρ → h.IsInvertible ∧
      ∀ j, IsDerivAt (fun z => (e' u z).left) 0 (h (Pi.single j 1))
        (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2) := fun u => by
    by_cases hu : u ∈ Metric.ball (0 : ℂ) ρ
    · obtain ⟨D, hD⟩ := exists_lieEquiv Z.t (hexp u hu).1 (hA u hu) (hexp u hu).2.2.2.2
      have ex : ∃ f : EigFrame Z ((ψ u).comp φ) (spMap (ψ u) ≫ (x ≫ genι Z)), ∀ τ i, f.v τ i = spMap (dualMap (ψ u)) ≫ fr.v τ i := by
        open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
        have h : GlobalTheory.LocM.IsFrame Z.t ((ψ u).comp φ) (spMap (ψ u) ≫ (x ≫ genι Z)) ((fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i)) := by
          letI : Algebra c.F A := φ.toAlgebra
          letI : Algebra c.F ℂ := ((ψ u).comp φ).toAlgebra
          let v : ∀ τ, Fin (Dw.mult τ) → TanM (x ≫ genι Z) Z.t.G := fun τ i => tanOf (fr.tan τ i)
          have eps_dual (a : A) : spMap (dualMap (ψ u)) ≫ spMap (epsMul a) = spMap (epsMul ((ψ u) a)) ≫ spMap (dualMap (ψ u)) := by
            rw [spMap_comp_spMap, spMap_comp_spMap]
            congr 1
            refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]
          have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
              spMap (epsMul (((ψ u).comp φ) (embK c τ a))) ≫ (fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i) τ i := fun τ i a => by
            show (spMap (dualMap (ψ u)) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (dualMap (ψ u)) ≫ fr.v τ i
            rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
          have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
            exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
          have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM (ψ u) (v k.1 k.2) := by
            have h := full_equiv (eB Dw).symm (full_bc (ψ u) (full_equiv (eB Dw) h1))
            exact (funext fun k => congrArg (fun j : IxB Dw => resM (ψ u) (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
          refine ⟨fun τ i => ⟨isTan_map (ψ u) rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
          have h3 := eig_of_full c (fun τ i => resM (ψ u) (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
            ((eig_iff c τ _).1 hwe)
          exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM (ψ u) (v τ i)) a (tanOf hw)).2 h3
        exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
      let f := Classical.choose ex
      have hf := Classical.choose_spec ex
      obtain ⟨b, hb⟩ := exists_basis f
      refine ⟨((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv, fun _ => ⟨⟨_, rfl⟩, fun j => ?_⟩⟩
      have h1 := hD (D.symm (f.vec (e j).1 (e j).2))
      rw [D.apply_symm_apply] at h1
      have h2 : ((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv (Pi.single j 1) =
          D.symm (f.vec (e j).1 (e j).2) := by simp [hb, Pi.single_apply]
      rw [← hf, ContinuousLinearEquiv.coe_coe, h2]
      exact h1
    · exact ⟨0, fun h => absurd h hu⟩
  choose h hh using hh
  refine ⟨h, fun u hu => ⟨(hh u hu).1, ?_, fun ex hadd hex hd z => ?_⟩⟩
  · refine ((hh u hu).1.contDiffAt_map_inverse (n := 1)).continuousAt.comp (continuousAt_clm_apply.2 fun z => ?_)
    have : ∀ u, h u z = ∑ j, z j • h u (Pi.single j 1) := fun u => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_smul, ← map_sum]
      exact congrArg _ (pi_eq_sum_univ' z)
    simp only [this]
    refine tendsto_finsetSum _ fun j _ => ContinuousAt.const_smul ?_ (z j)
    exact continuousAt_dir (e := e') (w := fun b => h b (Pi.single j 1))
      (v := fun b => spMap (dualMap (ψ b)) ≫ fr.v (e j).1 (e j).2) hol hu (hexp u hu).2.2.2.2 (fun b hb => (hh b hb).2 j) (continuousAt_snd (fun a =>
      ((harc.1.2 a).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hu))).continuousAt) _)
  · obtain ⟨hu1, -, hu2, -, hu3⟩ := hexp u hu
    obtain ⟨k, hk, -⟩ := existsUnique_linear hadd hu1 hex hu2 hu3
    have hkh : k = (h u).toLinearMap := (Pi.basisFun ℂ (Fin g)).ext fun i => by
      have h1 := (isDerivAt0_iff _ _ _).1 (hd i)
      simp only [hk] at h1
      have h2 := (isDerivAt_comp_iff (hA u hu) (LinearMap.toContinuousLinearMap k) _ _).1 h1
      rw [Pi.basisFun_apply]
      exact (hu3 (Over.homMk _ h2.over) h2.1).unique ((isDerivAt0_iff _ _ _).2 h2)
        ((isDerivAt0_iff _ _ _).2 ((hh u hu).2 i))
    rw [hk, hkh, ContinuousLinearMap.coe_coe]

end GlobalTheory.ShFam.BdArc
