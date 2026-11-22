module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.Columns.FiniteDimensionalForms

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev Pt (F : GFam K) : Type := Σ b, F.D b

def cls (F : GFam K) (p : F.Pt) : F.Cl := ⟨p.1, (F.mem p.1).cls p.2⟩

structure Ev (F : GFam K) (σ : K →+* ℂ) where

  Y : Type

  ev : F.V →ₛₗ[σ] (Y → ℂ)
  li : LinearIndependent ℂ fun i => ev (F.bV i)

  ip : (Y → ℂ) →ₗ⋆[ℂ] (Y → ℂ) →ₗ[ℂ] ℂ
  ip_ev : ∀ x y, ip (ev x) (ev y) = σ (F.pair x y)

  tr : ∀ b, F.G b →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ))
  tr_ev : ∀ b g x, tr b g (ev x) = ev (F.ρ b g x)

namespace Ev

variable {F : GFam K} {σ : K →+* ℂ} (E : F.Ev σ)


end Ev

end GFam

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end GSD.Ev

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]

end Round

end Formalism.L2.Col
