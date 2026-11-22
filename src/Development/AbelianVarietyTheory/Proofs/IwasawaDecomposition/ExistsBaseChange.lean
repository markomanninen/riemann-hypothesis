module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem GlobalTheory.ShFam.EigFrame.exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
