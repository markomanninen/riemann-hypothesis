module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWAniso

section Coord

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)] {n m : ℕ}


end Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}


end GlobalTheory.SWAniso

namespace GlobalTheory.Published

def SiegelWeilAnisotropicCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → n < m →
  ∀ X : Spc F E n, IsHermND σ X.J → X.L.IsLattice E →
    (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) → (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) →
  ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J → X₂.L = sumLat finSumFinEquiv X.L X.L →
    (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
  ∀ W : Spc F E m, (∀ i j, σ (W.J j i) = -W.J i j) → (∀ x, form σ W.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin (n + n) × Fin m),
    (∀ x : Matrix (Fin (n + n)) (Fin m) E, ∃ y z : Fin (n + n) × Fin m → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ j, uᵀ j ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X₂ W, IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) co 1 χ om →
  ∀ K : Subgroup (UA σ X₂.J), IsStab B K →
    IwasawaOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin (n + n) × Fin m), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (k, 1) Φ}) →
  ∀ (ν : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 ν →
    let P : Subgroup (UA σ X₂.J) := siegelOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ X₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J)).subtype (absE F E) K (fun g => om (g, 1) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ g h) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ X₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ X₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ X₂.J) (f s) g) s₀ (⨍ h in 𝓕, theta om Φ g h ∂ν)

end GlobalTheory.Published

end
