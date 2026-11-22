module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

@[expose] public section

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

def IsIdTorusElt (l : Fin r → (AF F ⊗[F] E)ˣ) (a : GAd σ J) : Prop :=
  (matHom _ σ J a).1 * adMat F X = adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  (matHom _ σ J a).1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ, (matHom _ σ J a).1 *ᵥ z = z



end GlobalTheory.IdTorus
