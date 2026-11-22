module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_equivariant_real_points : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  let w : M.Vec := fun τ => ⟨M.rep τ (g τ) (v τ : M.H τ),
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2⟩
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have h := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _
      (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at h
    exact h
  refine ⟨w, fun τ => rfl, fun U hU => ?_⟩
  rw [← hb]
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have equivOnList (l : List D.what₂.Tau) (hl : l.Nodup) :
        U (fun τ => if τ ∈ l then w τ else v τ) =
          rTr V (l.map fun τ => atTau θ V τ (g τ)).prod (U v) := by
      induction l with
      | nil =>
        funext x
        simp [rTr]
      | cons τ l ih =>
        rw [List.nodup_cons] at hl
        have h := hU.equiv τ (g τ) (hg τ) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w τ) (by
          simp only [if_neg hl.1]
          rfl)
        rw [ih hl.2] at h
        have hprod : rTr V ((τ :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
            rTr V (atTau θ V τ (g τ)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
          funext x
          simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        rw [hprod, ← h]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst ρ
          simp
        · rw [Function.update_of_ne hρ]
          simp [hρ]
    have h := equivOnList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [GlobalTheory.AdelicScalar.realElt, ← h]
    congr 1
    funext τ
    simp
  | zero =>
    funext x
    simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have h1x := congrFun h1 x
    have h2x := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at h1x h2x ⊢
    rw [h1x, h2x]
  | smul c U _ h =>
    funext x
    have hx := congrFun h x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at hx ⊢
    rw [hx]
