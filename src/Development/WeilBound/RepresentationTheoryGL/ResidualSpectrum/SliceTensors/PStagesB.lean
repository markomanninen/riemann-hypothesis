module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.ProjectionSandwichLength

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem absC_mul (s t : ℂ) : Model.absC E s * Model.absC E t = Model.absC E (s + t) := by
  apply Subtype.ext
  ext x
  change Complex.exp (s * _) * Complex.exp (t * _) = Complex.exp ((s + t) * _)
  rw [← Complex.exp_add, add_mul]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isAbsPow_absC (x : ℝ) : (Model.absC E (x : ℂ)).IsAbsPow x :=
  GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow x

omit [_root_.NumberField.IsTotallyComplex E] in
theorem eq_absC {ν : HChar E} {x : ℝ} (h : ν.IsAbsPow x) : ν = Model.absC E (x : ℂ) :=
  PositivityTheory.RSHS.ProjectionSandwichLength.eq_of_isAbsPow h (isAbsPow_absC x)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem chiDet_leviEmb {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) (χ : HChar E) (m : ∀ i, GA E (n i)) :
    ((chiDet N χ (leviEmb (Ad E) (stdBlocks n h) m) : ℂˣ) : ℂ) = ∏ i, ((chiDet (n i) χ (m i) : ℂˣ) : ℂ) := by
  classical
  have hp : leviEmb (Ad E) (stdBlocks n h) m ∈ parab (Ad E) (stdBlocks n h) := by
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
  have hd := det_parab (Ad E) (stdBlocks n h) ⟨leviEmb (Ad E) (stdBlocks n h) m, hp⟩
  have he : leviProj (Ad E) (stdBlocks n h) ⟨leviEmb (Ad E) (stdBlocks n h) m, hp⟩ = m := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [he] at hd
  change ((χ.1 (Matrix.GeneralLinearGroup.det (leviEmb (Ad E) (stdBlocks n h) m)) : ℂˣ) : ℂ) = _
  rw [hd, map_prod, Units.coe_prod]
  rfl

theorem tensorForms_mulChi {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i)) (χ : HChar E)
    {G : (∀ i, GA E (n i)) → ℂ} (hG : G ∈ tensorForms π) :
    (fun m => G m * ∏ i, ((chiDet (n i) χ (m i) : ℂˣ) : ℂ)) ∈ tensorForms (fun i => (π i).twist χ) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine Submodule.subset_span ⟨fun i => ⟨mulChi (n i) χ (φ i).1, ⟨(φ i).1, (φ i).2, rfl⟩⟩, funext fun m => ?_⟩
    simp only [mulChi_apply, Finset.prod_mul_distrib]
  | zero =>
    convert zero_mem (tensorForms fun i => (π i).twist χ) using 1 <;> funext m <;> simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp [mul_assoc]

theorem tensorForms_append {d₁ d₂ a : ℕ} (π : Fin (d₁ + d₂) → CuspSub E a) {G₁ : (Fin d₁ → GA E a) → ℂ}
    {G₂ : (Fin d₂ → GA E a) → ℂ} (h₁ : G₁ ∈ tensorForms (n := fun _ => a) (fun b => π (Fin.castAdd d₂ b)))
    (h₂ : G₂ ∈ tensorForms (n := fun _ => a) (fun b => π (Fin.natAdd d₁ b))) :
    (fun m : Fin (d₁ + d₂) → GA E a => G₁ (fun b => m (Fin.castAdd d₂ b)) * G₂ (fun b => m (Fin.natAdd d₁ b))) ∈
      tensorForms (n := fun _ => a) π := by
  induction h₁ using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, rfl⟩ := hF
    induction h₂ using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨φ₂, rfl⟩ := hF
      refine Submodule.subset_span ⟨Fin.addCases (motive := fun i => ↥(π i).V) φ₁ φ₂, funext fun m => ?_⟩
      simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]
    | zero =>
      convert zero_mem (tensorForms (n := fun _ => a) π) using 1 <;> funext m <;> simp
    | add F G _ _ hF hG =>
      convert add_mem hF hG using 1
      funext m
      simp [mul_add]
    | smul c F _ hF =>
      convert Submodule.smul_mem _ c hF using 1
      funext m
      simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  | zero =>
    convert zero_mem (tensorForms (n := fun _ => a) π) using 1 <;> funext m <;> simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

end PositivityTheory.Rg.Rs.InductionInStages

end
