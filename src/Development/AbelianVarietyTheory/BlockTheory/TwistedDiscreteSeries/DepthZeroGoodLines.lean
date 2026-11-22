module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses

section Finite

variable {F : Type} [Field F] {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y]

end Finite

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

def red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])

def diagOne (r t : ℕ) : GL (Fin r) 𝒪[k] →* GL (Fin (r + t)) k :=
  (emb₂ k (stdSum (rfl : r + t = r + t))).comp ((MonoidHom.inl _ _).comp (incl k r))

def unipLevel (r : ℕ) : Subgroup (GL (Fin r) 𝒪[k]) := (unipB 𝓀[k] (Fin r)).comap (red k r)

variable {k} {r t n : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def HasBlocks (h : GL (Fin (r + t)) 𝒪[k]) (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : Prop :=
  (∀ i j, h.val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j) ∧
  (∀ i j, h.val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j) ∧
  ∀ i j, h.val (Fin.natAdd r i) (Fin.castAdd t j) ∈ IsLocalRing.maximalIdeal 𝒪[k]

def IsDatum (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  (σ.IsIrreducible ∧ IsSmooth σ ∧ IsUnitarisable σ) ∧
    IsUnitaryChar χW ∧ IsUnitaryChar χV ∧ IsTame χW ∧ IsUnram (χW * χV⁻¹)

end Local

section Places

variable {ι : Type} [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, ValuativeRel (k v)]
  [∀ v, TopologicalSpace (k v)] [∀ v, IsNonarchimedeanLocalField (k v)] (r : ℕ)

variable {k r}

end Places

section Examples

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isDatum_detRep (r : ℕ) {χ χW χV : kˣ →* ℂˣ} (h : IsUnram χ) (hu : IsUnitaryChar χ)
    (hW : IsUnitaryChar χW) (hV : IsUnitaryChar χV) (ht : IsTame χW) (hr : IsUnram (χW * χV⁻¹)) :
    IsDatum (detRep (Fin r) χ) χW χV :=
  ⟨⟨isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 (GlobalTheory.SmGL.isSmoothChar_of_isUnram h).detChar,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩, hW, hV, ht, hr⟩

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses
