module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_darboux_coordinates_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  first | exact @GlobalTheory.SympChange.darboux_change_rat | exact GlobalTheory.SympChange.darboux_change_rat | (intros; apply GlobalTheory.SympChange.darboux_change_rat <;> assumption)
