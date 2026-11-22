module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

@[expose] public section

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.XiDetCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.CoefChangeCompare
open scoped TensorProduct

section Lattices

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

def latHat0 (L0 : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ x i}

def finVec (v : Fin r → E) : Fin r → AdE F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

variable {F}

def gLat (L0 : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Set (Fin r → AdE F E) :=
  g.mulVec '' (latHat0 F L0 : Set (Fin r → AdE F E))

def latG (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat L0 g ∧ w = a • v}

def latGHat (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat L0 g, w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a) * z i}

variable (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

end Lattices

section Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  [Fact (IsRealIn F E)] {r : ℕ}

def Reads (xi : (AdE F E)ˣ →* ℂˣ) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ x u : (AdE F E)ˣ, (x : AdE F E) = u * conjA F (x : AdE F E) → ((xi u : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)

def TrivFix (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1

def TrivRat (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1

end Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r rk : ℕ}
variable {𝔾 : Type} [Group 𝔾]

section First

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin rk) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin rk → E)) (AA : Set E)

def MarkedBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ}
    {lab : Fin g → E →+* ℂ} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (h γ : 𝔾) : Prop :=
  γ ∈ Γ ∧
    ((U.X (dict h).1).Λ : Set (Fin r → E)) =
      (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w

variable {Th : Type} (arch : Th → 𝔾 → Matrix (Fin rk) (Fin rk) ℂ)


variable (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (IsInf : (E →+* ℂ) → Th → Prop)

end First

section Mark

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def embOf (k : U.Comp) : (Fu.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap

variable {L0 AA ι}

end Mark

section Value

variable [Fact (IsRealIn F E)]

def XiValAtC {c : Coeff l} (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → toC (evR Xo c f y) = c0 * ((ξ x : Circle) : ℂ)


variable (Xo) in
def XiValC (c : Coeff l) (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAtC c0 Gm ι ξ σ Fu φ f

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) {L0 : Submodule (𝓞 E) (Fin r → E)} {AA : Set E}
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
  (ψ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E))

def Reaches (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ (i : Fin Fu.n) (gm : Matrix (Fin r) (Fin r) (AdE F E)), IsUnitaryA Gm gm → LatAt ι (ψ i) gm →
    MarkAt l ι (ψ i) (Fu.t i) gm → ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) lab P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → ∃ h : 𝔾, (fin h).1 = gm ∧ ik (dict h).1 = i ∧
        ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un (dict h).1 ⟨(dict h).2, hx⟩) y

variable {Γ fin U dict Fu ik φ ψ} {Gm : Matrix (Fin r) (Fin r) E} {xi : (AdE F E)ˣ →* ℂˣ} {ξ : (AdE F E)ˣ →* Circle}
  {c0 : ℂ} {f : Rul Xo c}

end Value

section Covers

variable [Fact (IsRealIn F E)] (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E))
  (AA : Set E) {Th : Type} (arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ) (IsInf : (E →+* ℂ) → Th → Prop)

variable {Γ fin L0 AA arch IsInf} {gram : Matrix (Fin r) (Fin r) E} {xi0 : E}

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : 𝔾 → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin Fu.n} {φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ} {th : ∀ k, (U.X k).Ψ → Th}

end One

variable {c : Coeff l} {σ0 : c.F →+* ℂ} {Tup : Type*} {dδ : Tup → DeltaDat Xo c n}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle} {c0 : ℂ}

end Covers

section Comparison₂

section Act

variable (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

variable {c} {c' : Coeff l} (hle : c.F ≤ c'.F)

end Act

variable (Γ : Subgroup 𝔾)



variable {c c' : Coeff l} (hle : c.F ≤ c'.F) {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

variable (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
  (dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
  (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)] (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
  (La : ∀ t, Cl' t → GenLat E n) (Nc gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F)
  (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
  (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
  (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ)

end Comparison₂

section Whole

variable [Fact (IsRealIn F E)] {Γ : Subgroup 𝔾} {fin : 𝔾 →* GL (Fin r) (AdE F E)} {L0 : Submodule (𝓞 E) (Fin r → E)}
  {AA : Set E} {Th : Type} {arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ} {IsInf : (E →+* ℂ) → Th → Prop}
  {gram : Matrix (Fin r) (Fin r) E} {xi0 : E} {c c' : Coeff l} {hle : c.F ≤ c'.F} {Vs : Type} [AddCommGroup Vs]
  [Module c'.F Vs] {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
  {dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r} {mu : 𝔾 → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)} {Tup : Type*} {dδ : Tup → DeltaDat Xo c' n}
  {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)] {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F}
  {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F}
  {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop}
  {cst : (U (sig0 c)).Comp → ℂ} {ph : ℂ}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((sig0 c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle}

end Whole

end GlobalTheory.XiDetCompare
