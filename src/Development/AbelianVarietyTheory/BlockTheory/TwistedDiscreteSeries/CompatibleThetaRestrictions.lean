module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.IndefR.Lift (liftInt)
open GlobalTheory.Cusp (constTerm frameFlag)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adel {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) (AE D) := x.map (incA D)

abbrev ct {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x

def IsWittStep (B B' : HSp D) (t : ℕ) (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) : Prop :=
  B'.rank + 2 * t = B.rank ∧ HSpace.IsIsomEmb B' B ι ∧ IsIsoSub B C ∧ ct (frameMat B B' ι) * B.gram * C = 0

theorem isWittLower_iff (B B' : HSp D) (t : ℕ) : IsWittLower B B' t ↔ ∃ ι C, IsWittStep B B' t ι C :=
  ⟨fun ⟨h, ι, h1, C, h2, h3⟩ => ⟨ι, C, h, h1, h2, h3⟩, fun ⟨ι, C, h, h1, h2, h3⟩ => ⟨h, ι, h1, C, h2, h3⟩⟩

theorem exists_isWittStep_iff (B : HSp D) (t : ℕ) :
    (∃ B' ι C, IsWittStep B B' t ι C ∧ B'.SigOK) ↔ t ≤ GlobalTheory.Cusp.wittIndex B := by
  rw [← GlobalTheory.Cusp.exists_isWittLower_iff]
  exact ⟨fun ⟨B', ι, C, h, h'⟩ => ⟨B', (isWittLower_iff _ _ _).2 ⟨ι, C, h⟩, h'⟩,
    fun ⟨B', h, h'⟩ => let ⟨ι, C, h⟩ := (isWittLower_iff _ _ _).1 h; ⟨B', ι, C, h, h'⟩⟩

def IsLeviElt (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E)
    (a : GL (Fin t) (AE D)) (h' : GA D B') (m : GA D B) : Prop :=
  HMul.hMul (Formalism.L2.Theta.mt B m) (adel C) = HMul.hMul (adel C) a.val ∧
    HMul.hMul (Formalism.L2.Theta.mt B m) (adel (frameMat B B' ι)) =
      HMul.hMul (adel (frameMat B B' ι)) (Formalism.L2.Theta.mt B' h')

def IsAutCharGL (t : ℕ) (μ : GL (Fin t) (AE D) →* Circle) : Prop :=
  Continuous μ ∧ ∀ a : GL (Fin t) D.host.E, μ (Matrix.GeneralLinearGroup.map (incA D) a) = 1

def IsAutCharU (V : HSp D) (ξ : GA D V →* Circle) : Prop := Continuous ξ ∧ ∀ γ ∈ GQ V, ξ γ = 1

def detPow {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : ℝ :=
  (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((n : ℝ) / 2)

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

section Target

variable (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V)
  (C : Matrix (Fin T.rank) (Fin t) D.host.E)

def resT (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ :=
  fun w' => ∫ y in 𝓖, φ (adel C * (y : Matrix (Fin t) (Fin S.rank) (AE D)) +
    adel (frameMat T T' ι) * (w' : Matrix (Fin T'.rank) (Fin S.rank) (AE D))) ∂μ

end Target

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) (S S' T : HSp D) {t : ℕ} (ι : S'.V →ₗ[D.host.E] S.V)
  (C : Matrix (Fin S.rank) (Fin t) D.host.E)

def resS (μ : Measure (Mx D T.rank t)) (𝓖 : Set (Mx D T.rank t)) (φ : WO S T → ℂ) : WO S' T → ℂ :=
  fun w' => ∫ y in 𝓖, φ ((y : Matrix (Fin T.rank) (Fin t) (AE D)) * adel (ct C * S.gram) +
    (w' : Matrix (Fin T.rank) (Fin S'.rank) (AE D)) * adel (S'.gram⁻¹ * ct (frameMat S S' ι) * S.gram)) ∂μ

end Source

end GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

end
