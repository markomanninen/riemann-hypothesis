module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dblEmb {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) : Matrix (Fin n ⊕ Fin n) (Fin n₁ ⊕ Fin n₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Matrix.fromBlocks ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι) 0 0 ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)

def isoD (d : ℕ) {n n₁ : ℕ} (H : Plane E n n₁) : Set (Matrix (Fin d) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | ∃ z₁ z₂ : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), u = Matrix.vecMulVec z₁ (Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
    Matrix.vecMulVec z₂ (Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x))}

def IsDLevi {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (H : Plane E n n₁)
    (gd₁ : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁))) (md : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J))) : Prop :=
  md.1.1 *ᵥ Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ∧
  md.1.1 *ᵥ Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x) = Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x) ∧
  md.1.1 * dblEmb H.ι = dblEmb H.ι * gd₁.1.1

def IsDblOf (ψ : AddChar (AF F) ℂ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χW : Chr F E)
    (om : Rep σ X W)
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)) : Prop :=
  ∃ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d), (∀ x, d'.e xᵀ = M.co.e x) ∧
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd ∧
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) dd χW (diagCols (Fin n)) omd ∧
    ∀ (g : UA σ X.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))),
      gd.1.1 = Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂

theorem exists_isDblOf {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') :
    ∃ dd omd, IsDblOf B.ψ M χW om dd omd := by
  obtain ⟨-, ⟨d', hd', -, dd, omd, h1, h2, h3⟩, -⟩ := hP.weil
  exact ⟨dd, omd, d', hd', h1, h2, fun g gd hgd φ₁ h₁ φ₂ h₂ => h3 g gd hgd φ₁ h₁ φ₂ h₂⟩

end GlobalTheory.MixXChar

end
