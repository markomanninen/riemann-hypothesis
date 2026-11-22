module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open scoped ENNReal Matrix

def len_vp (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  (Module.length O M : ℝ≥0∞) / (Module.length O (O ⧸ Ideal.span {(l : O)}) : ℝ≥0∞)

def val_vp {O : Type} [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ :=
  len_vp O l (O ⧸ Ideal.span {x})

section Rep

variable {Γ A : Type} [Group Γ] [CommRing A] {m : ℕ}

end Rep

section Div

variable {Γ O' : Type} [Group Γ] [CommRing O'] [IsDomain O'] {m : ℕ}

end Div

section BK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

def IsCrysCocycle (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) (f : ↥Gw → Fin m → O₀) : Prop :=
  (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) => Bw.toLL (f (Bw.e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))

variable {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')

end BK

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev decAt (v : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 v)

abbrev ineAt (v : PlE D.host) : Subgroup (GE D) := Ine (F := D.host.E) (D.nd.plOm.1 v)

def InertiaBound (ε' : ℝ) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∀ γ : PlE D.host → GE D, (∀ P ∈ Q, TameGenAt (D.nd.plOm.1 P) (γ P)) →
    (D.R.t : ℝ≥0∞) * ∑ P ∈ Q, val_vp (D.ntw.l i) (((ψ (γ P) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) - 1) ≤
      ENNReal.ofReal ε'

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
