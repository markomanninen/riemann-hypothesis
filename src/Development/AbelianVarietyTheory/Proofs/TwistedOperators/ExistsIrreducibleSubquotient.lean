module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section General

variable {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


end Local

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod]
    simp only [h, MultilinearMap.map_smul_univ, RingHom.id_apply]
    rw [smul_comm]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have h1 : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) :=
    fun a => by ext; simp [GeneralLinearGroup.scalar]
  have h2 : ∑ a, modExp m a * (Fintype.card (m a) : ℤ) = 0 := by
    simp only [modExp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_filter, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    simp only [mul_comm]
  apply Units.ext
  rw [val_deltaHalf, modulus]
  have h3 : ∀ a, nabs k (z ^ Fintype.card (m a)) ^ modExp m a =
      nabs k z ^ (modExp m a * (Fintype.card (m a) : ℤ)) := fun a => by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast]
    simp [nabs]
  simp only [h1, h3, ← Real.rpow_intCast]
  rw [← Real.rpow_sum_of_pos (nabs_pos' k z), ← Int.cast_sum, h2]
  simp

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp [leviEmb, blockDiagonal'_apply_eq, GeneralLinearGroup.scalar, diagonal_apply]
    · simp [leviEmb, blockDiagonal'_apply_ne _ _ _ hab, GeneralLinearGroup.scalar,
        diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have hm : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) ∈ parab k e := by
    apply mem_parab_iff.2
    intro a b i j hab
    rw [h1]
    simp [GeneralLinearGroup.scalar, diagonal_apply, hab.ne']
  have hp : leviProj k e ⟨_, hm⟩ = (fun a => GeneralLinearGroup.scalar (m a) z) := by
    funext a
    ext i j
    simp [leviProj, diagBlock, leviEmb, GeneralLinearGroup.scalar, diagonal_apply]
  have h2 := parInd_law e _ f ⟨_, hm⟩ x
  rw [hp, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
