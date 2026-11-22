module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (σ) in
def finK {n : ℕ} (W : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : Set (UA σ W.J) :=
  {x | ∃ k ∈ KInf σ W τ, ∃ g ∈ UAt σ W (fun u : AF F => u.2), x = k * g}

variable {a a' : ℕ}

structure InducedMaj (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop where
  cartan : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)
  tie : ∀ w, ∃ a : Fin n₁ → ℂ, Y.θ w * (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) =
    (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) * Y₁.θ w

theorem InducedMaj.of_comm {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w))
    (h₂ : ∀ w, Y.θ w * H.ι.map (B.emb w).1 = H.ι.map (B.emb w).1 * Y₁.θ w) : InducedMaj B H Y Y₁ :=
  ⟨h₁, fun w => ⟨0, by
    have e : Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) (0 : Fin n₁ → ℂ) = 0 := by ext; simp [Matrix.vecMulVec_apply]
    rw [e, add_zero]; exact h₂ w⟩⟩


variable (σ) in
def IsIsoPlane (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
    (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) ∧ InducedMaj B H Y Y₁

theorem IsIsoPlane.of_adapted {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w))
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) : IsIsoPlane σ B H Y Y₁ :=
  ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, h, .of_comm h₁ fun w => (hH.cartan w).1⟩

end GlobalTheory.ThK.DescB

end
