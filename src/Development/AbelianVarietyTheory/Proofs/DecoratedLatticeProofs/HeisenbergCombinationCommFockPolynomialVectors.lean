module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFiniteHeis

variable {D : D7}

theorem foldr_lin {ι X : Type} (p : (X → ℂ) → Prop) (A : ι → (X → ℂ) → (X → ℂ))
    (hp : ∀ i f, p f → p (A i f)) (hadd : ∀ i f g, p f → p g → A i (f + g) = A i f + A i g)
    (hsmul : ∀ i (c : ℂ) f, p f → A i (c • f) = c • A i f) (padd : ∀ f g, p f → p g → p (f + g))
    (psmul : ∀ (c : ℂ) f, p f → p (c • f)) (c : ℂ) {f g : X → ℂ} (hf : p f) (hg : p g) (l : List ι) :
    l.foldr (fun i h => A i h) (c • f + g) = c • l.foldr (fun i h => A i h) f + l.foldr (fun i h => A i h) g := by
  have hm : ∀ l : List ι, p (l.foldr (fun i h => A i h) f) ∧ p (l.foldr (fun i h => A i h) g) := by
    intro l
    induction l with
    | nil => exact ⟨hf, hg⟩
    | cons i l ih => exact ⟨hp i _ ih.1, hp i _ ih.2⟩
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, hadd i _ _ (psmul c _ (hm l).1) (hm l).2,
      hsmul i c _ (hm l).1]

theorem pureTensorO_lin (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : ℂ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f + g) φ =
      c • pureTensorO ψ θ S T sS sT BS BT f φ + pureTensorO ψ θ S T sS sT BS BT g φ := by
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := by
    refine {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          obtain ⟨U', hU', h2⟩ := hg.level
          refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu.1 h0) w
          have e2 := congrFun (h2 u hu.2 h0) w
          unfold heisO at e1 e2 ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
        cont := hf.cont.add hg.cont
        smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

    }
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          unfold heisO at e1 ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        cont := hf.cont.const_smul c
        smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
    }
  have h : pureTensorO ψ θ S T sS sT BS BT (c • f + g) =
      c • pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT g := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    unfold pureTensorO pureTensorL
    rw [Module.Basis.constr_basis, Module.Basis.constr_basis, Module.Basis.constr_basis]
    unfold opPow
    have A1 : ∀ k f, IsThetaFunO ψ S T f →
        IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f) :=
      fun k f hf => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf
    have A2 : ∀ k f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (f + g) =
          aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f +
            aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g :=
      fun k f g hf hg => GlobalTheory.FockIndep.aPlus_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf hg
    have A3 : ∀ k (c : ℂ) f, IsThetaFunO ψ S T f →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (c • f) =
          c • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f :=
      fun k c f hf => GlobalTheory.FockIndep.aPlus_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ c hf
    exact foldr_lin (IsThetaFunO ψ S T) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) A1 A2 A3
      (fun _ _ hf hg => theta_add hf hg) (fun c _ hf => theta_smul c hf) c hf hg _
  rw [h, LinearMap.add_apply, LinearMap.smul_apply]

end GlobalTheory.FockFiniteHeis

namespace GlobalTheory.FockFiniteHeis

theorem pureTensorO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have h := pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (-1) theta_zero theta_zero φ
  rwa [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h

theorem heis_comb_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ sS sT BS BT (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0) → ∀ φ, ∑ i, a i • heisO ψ S T (y i) (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT (∑ i, a i • heisO ψ S T (y i) f) φ ∧ pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  intro D ψ θ S T hψ hθ sS sT BS BT f hf n a y hy φ
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := by
    refine {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          obtain ⟨U', hU', h2⟩ := hg.level
          refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu.1 h0) w
          have e2 := congrFun (h2 u hu.2 h0) w
          unfold heisO at e1 e2 ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
        cont := hf.cont.add hg.cont
        smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

    }
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          unfold heisO at e1 ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        cont := hf.cont.const_smul c
        smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
    }
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f hf
  have hth : ∀ i, IsThetaFunO ψ S T (heisO ψ S T (y i) f) := fun i => (ft.2 (y i) (hy i)).1
  have key : ∀ s : Finset (Fin n), IsThetaFunO ψ S T (∑ i ∈ s, a i • heisO ψ S T (y i) f) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • heisO ψ S T (y i) f) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T (y i) f) φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ⟨theta_zero, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine ⟨theta_add (theta_smul _ (hth i)) ih.1, ?_⟩
      rw [pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hth i) ih.1 φ, ih.2]
  refine ⟨?_, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  rw [(key Finset.univ).2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(ft.2 (y i) (hy i)).2 sS BS sT BT φ]

end GlobalTheory.FockFiniteHeis

end
