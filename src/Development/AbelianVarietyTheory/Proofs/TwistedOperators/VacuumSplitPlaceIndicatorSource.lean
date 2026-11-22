module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorBase
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDiagonalStabilizerGeneratedHermitianDoStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitVacV
open GlobalTheory.DblVacSiegel

theorem siegel_eigen_eq_one_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv d' dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *
          ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt (X.β / X.α) P := fun P hP => by
    have hPT : P ∉ above E (X.T : Set (Pl (F := F))) := fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))))
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ P hPT).mul (hT.chars.unrα P hPT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.V hT.geo.hV.lat hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (u • ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  have he := congrArg (DiagForm.lDiag F (Fin a × Fin (a + a'))) hμ
  rw [map_smul, smul_eq_mul] at he
  rw [hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl (he.symm.trans hrule)
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

end GlobalTheory.SplitVacV

end
