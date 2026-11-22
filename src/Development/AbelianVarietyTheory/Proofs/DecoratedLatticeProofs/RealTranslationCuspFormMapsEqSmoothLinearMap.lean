module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitGramAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealTransSm

open Formalism.MainNotions.StandardLattice

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem infMat_list_prod (hθ : IsInfFam θ) (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    ∀ l : List D.what₂.Tau, l.Nodup →
      infMat D.sp.cm.sig V.gram (θ ρ) (l.map fun τ => atTau θ V τ (u τ)).prod = if ρ ∈ l then u ρ else 1
  | [], _ => by simpa using GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_list_prod hθ u hu ρ l hl.2]
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V a (hu a)
    by_cases c : ρ = a
    · subst c
      rw [hs.2.1, ite_eq_right hl.1, ite_eq_left List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      by_cases d : ρ ∈ l
      · rw [ite_eq_left d, ite_eq_left (List.mem_cons_of_mem a d)]
      · rw [ite_eq_right d, ite_eq_right]
        simp [c, d]

theorem eq_realElt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    g = GlobalTheory.AdelicScalar.realElt θ V (fun τ => infMat D.sp.cm.sig V.gram (θ τ) g) := by
  set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) g with hu_def
  have hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  set P := GlobalTheory.AdelicScalar.realElt θ V u with hP
  have hPm : P ∈ GinfC V := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem V τ (u τ)
  have e : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) P = infMat D.sp.cm.sig V.gram (θ ρ) g := fun ρ => by
    rw [hP, GlobalTheory.AdelicScalar.realElt, infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
      ite_eq_left (Finset.mem_toList.2 (Finset.mem_univ ρ))]
  refine mul_inv_eq_one.1 (GlobalTheory.PointAtPlace.eq_one_of_mem V _ ((GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 _ fun ρ => ?_)
    (mul_mem hg (inv_mem hPm)))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

def smAct (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (τ : D.what₂.Tau) :
    M.sm τ →ₗ[ℂ] M.sm τ :=
  (M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) g)).toLinearMap.restrict fun _ hw =>
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ) hw

theorem rTrans_eq_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → ∀ g ∈ GinfC V, ∃ σ : SmT M →ₗ[ℂ] SmT M, ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ MultT θ M J χ, ∀ x, T (σ x) = rTrans g (T x) := by
  intro D θ V S M hθ g hg
  refine ⟨PiTensorProduct.map (smAct hθ M g), fun J χ T hT x => ?_⟩
  have hU : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod]
    let u τ := infMat D.sp.cm.sig V.gram (θ τ) g
    let w : M.Vec := fun τ => smAct hθ M g τ (v τ)
    have hu (τ : D.what₂.Tau) : u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have hw (τ : D.what₂.Tau) : (w τ : M.H τ) = M.rep τ (u τ) (v τ : M.H τ) := rfl
    have translate (U : MMap M) (hU : U ∈ Mult θ M J χ) :
        U w = rTr V (GlobalTheory.AdelicScalar.realElt θ V u) (U v) := by
      induction hU using Submodule.span_induction with
      | mem U hU =>
        have onList (l : List D.what₂.Tau) (hl : l.Nodup) :
            U (fun τ => if τ ∈ l then w τ else v τ) =
              rTr V (l.map fun τ => atTau θ V τ (u τ)).prod (U v) := by
          induction l with
          | nil =>
            funext h
            simp [rTr]
          | cons a l ih =>
            rw [List.nodup_cons] at hl
            have ha := hU.equiv a (u a) (hu a) (fun τ => if τ ∈ l then w τ else v τ)
              (w a) (by simpa only [ite_eq_right hl.1] using hw a)
            rw [ih hl.2] at ha
            have hupdate : (fun τ => if τ ∈ a :: l then w τ else v τ) =
                Function.update (fun τ => if τ ∈ l then w τ else v τ) a (w a) := by
              funext τ
              by_cases hτ : τ = a
              · subst τ
                simp
              · rw [Function.update_of_ne hτ]
                simp [hτ]
            rw [hupdate, ha]
            funext h
            simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        have hall := onList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
        simpa [GlobalTheory.AdelicScalar.realElt] using hall
      | zero => funext h; simp [rTr]
      | add U U' _ _ h₁ h₂ =>
        funext h
        simpa only [rTr, add_apply, Pi.add_apply] using
          congrArg₂ (· + ·) (congrFun h₁ h) (congrFun h₂ h)
      | smul a U _ h₁ =>
        funext h
        simpa only [rTr, smul_apply, Pi.smul_apply] using
          congrArg (a • ·) (congrFun h₁ h)
    have key := translate _ hU
    have hreal : GlobalTheory.AdelicScalar.realElt θ V u = g := (eq_realElt hθ hg).symm
    rw [hreal, PiTensorProduct.lift_symm] at key
    simp only [LinearMap.compMultilinearMap_apply] at key
    change c • T (PiTensorProduct.tprod ℂ w) = _
    funext h
    simp only [key, rTr, rTrans, map_smul, Pi.smul_apply]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    funext h
    simp [rTrans]

end GlobalTheory.RealTransSm

end
