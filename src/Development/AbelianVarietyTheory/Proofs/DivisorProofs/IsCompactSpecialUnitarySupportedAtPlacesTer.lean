module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesBis
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)), IsCompact X → IsClosed (SUSupp σ J ε) → (∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp <;> assumption)
