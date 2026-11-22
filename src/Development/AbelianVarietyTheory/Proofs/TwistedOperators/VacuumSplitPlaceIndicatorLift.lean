module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_inFin (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (inFin v a) := by
  intro u hu
  have h := GlobalTheory.InertDetChr.at_inFin_one (F := F) v u hu
  rw [smul_eq_mul] at h ⊢
  rw [show a = 1 * a from (one_mul a).symm, inFin_mul, ← mul_assoc, h, zero_mul]

theorem compFin_smul_inclR (v : Pl (F := F)) (a : AF F) (y : E) :
    compFin F E v (a • inclR (F := F) (AF F) y) = evFin F v a ⊗ₜ[F] y := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.InertDetChr.compFin_algebraMap]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this]
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem comp_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : compFin F E v ∘ z ∈ latLoc F W.L v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    convert tmul_mem_latLoc ha hy using 1
    funext i
    exact compFin_smul_inclR v a (y i)
  | zero =>
    convert zero_mem (latLoc F W.L v) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem mulVec_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ y ∈ latLoc F W.L v, (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v := by
  intro y hy
  refine latLoc_induction (p := fun y => (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v)
    (fun a ha x hx => ?_) (by rw [Matrix.mulVec_zero]; exact zero_mem _)
    (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h')
    (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hy
  have hz : (inFin v a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt W v :=
    AddSubgroup.subset_closure ⟨inFin v a, at_inFin v a, by rwa [GlobalTheory.InertDetChr.evFin_inFin_self], x, hx, rfl⟩
  have e1 : (fun i => a ⊗ₜ[F] x i) = compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i)) := by
    funext i
    show _ = compFin F E v (inFin v a • inclR (F := F) (AF F) (x i))
    rw [compFin_smul_inclR, GlobalTheory.InertDetChr.evFin_inFin_self]
  rw [e1]
  have e2 : (compFin F E v).mapMatrix g *ᵥ (compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) =
      compFin F E v ∘ (g *ᵥ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) :=
    funext fun i => (RingHom.map_mulVec (compFin F E v) g _ i).symm
  rw [e2]
  exact comp_mem_latLoc W v (hg _ hz)

theorem det_mem_intLoc {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl (F := F)} (P : GL (Fin d) (Fv F v ⊗[F] E))
    (hP : ∀ y : Fin d → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ P.1 *ᵥ y ∈ latLoc F L v)
    (g : GL (Fin d) (Fv F v ⊗[F] E)) (hg : ∀ y ∈ latLoc F L v, g.1 *ᵥ y ∈ latLoc F L v) :
    ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  set Q : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E) := (P⁻¹ * g * P).1 with hQ
  have hent : ∀ i j, Q i j ∈ intLoc F E v := by
    intro i j
    have h1 : P.1 *ᵥ (Pi.single j 1) ∈ latLoc F L v := (hP _).1 (fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e])
    have h2 := (hP (Q *ᵥ Pi.single j 1)).2 (by
      rw [hQ, Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul,
        ← Matrix.mulVec_mulVec]
      exact hg _ h1)
    have := h2 i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  let Q' : Matrix (Fin d) (Fin d) (intLoc F E v) := fun i j => ⟨Q i j, hent i j⟩
  have hQ' : (intLoc F E v).subtype.mapMatrix Q' = Q := rfl
  have hdet : Q.det = ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    rw [hQ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm _ (Matrix.GeneralLinearGroup.det P), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hdet, ← hQ', ← RingHom.map_det]
  exact (Matrix.det Q').2

end GlobalTheory.SplitDetChr
