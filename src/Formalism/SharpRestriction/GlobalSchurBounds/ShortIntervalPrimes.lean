module

public import Mathlib
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField Filter Topology MeasureTheory

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-(c * Real.log X / Real.log B)) + C * Real.exp (-(c * Real.sqrt (Real.log X)))

section RayClass

variable (K0 : Type) [Field K0] [NumberField K0]

def CoprimeTo (qq I : Ideal (𝓞 K0)) : Prop := I ≠ ⊥ ∧ I ⊔ qq = ⊤

def RayRel (qq I J : Ideal (𝓞 K0)) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I = Ideal.span {b} * J

def Bmod (qq : Ideal (𝓞 K0)) : ℝ := 4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

def nDeg1 (qq I0 : Ideal (𝓞 K0)) (X h : ℝ) : ℕ :=
  Set.ncard {P : Ideal (𝓞 K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
    (Ideal.absNorm P).Prime ∧ X < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ X * (1 + h)}

def ShortIntervalLowerBound (cQ C0 Cr cr c1 c2 : ℝ) : Prop :=
  ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ → ∀ X : ℝ, Bmod K0 qq ^ C0 ≤ X →
    (∀ (be : ℝ) (th : ℤ), (th = -1 ∨ th = 0 ∨ th = 1) → 1 / 2 ≤ be → be < 1 →
      cQ / (Bmod K0 qq ^ 2 * Real.log (Bmod K0 qq)) ≤ 1 - be →
      c1 * Bmod K0 qq ^ (-5 : ℝ) * X / Real.log X ≤ Li X - (th : ℝ) * Li (X ^ be)) ∧
    (∀ I0, CoprimeTo K0 qq I0 → ∀ h : ℝ, rhoErr Cr cr (Bmod K0 qq) X ≤ h / 100 → h ≤ 1 →
      Bmod K0 qq ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
      c2 * h * Bmod K0 qq ^ (-6 : ℝ) * X / Real.log X ≤ (nDeg1 K0 qq I0 X h : ℝ))

end RayClass

def NormOneMod (D : D7) (M g : ℕ) : Prop :=
  ∃ π ρ : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (ρ : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) - 1 = (M : D.host.E) * ρ ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (g : D.host.E)

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

abbrev ZPt : Type := Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ

def zOrd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def adm6 (_D : D7) (C1 c : ℝ) : Prop :=
  (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset ZPt,
    (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧
      DirichletCharacter.LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) →
    ((∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤
      C1 * Q ^ ((1 : ℝ) / 4)) ∧
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ,
    DirichletCharacter.LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re →
    IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 1 ∧
      ∀ ρ' : ℂ, DirichletCharacter.LFunction χ ρ' = 0 →
        1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
  (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3))

def adm7 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖)

def adm11 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (zOrd χ ρ : ℝ) ≤ C * Real.log (N * (|t| + 2))

theorem factorsThrough_inv {N : ℕ} {χ : DirichletCharacter ℂ N} {d : ℕ}
    (h : χ.FactorsThrough d) : χ⁻¹.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive DirichletCharacter.conductor at *
  have hs : χ⁻¹.conductorSet = χ.conductorSet := by
    ext d
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.mem_conductorSet_iff]
    exact ⟨fun h' => by simpa using factorsThrough_inv h', factorsThrough_inv⟩
  rw [hs]
  exact h

theorem zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hprim := isPrimitive_inv hχ
  have hρ0 : ρ ≠ 0 := fun h => by
    rw [h] at h0
    simp at h0
  have h1ρ : (1 - ρ) ≠ 0 := fun h => by
    have e := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at e
    linarith
  have hg : DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have e := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ) ρ (Or.inl hρ0)
    rw [hz, eq_comm, div_eq_zero_iff] at e
    exact e.resolve_right hg
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹) (1 - ρ) (Or.inl h1ρ),
    hprim.completedLFunction_one_sub ρ, inv_inv, hc]
  simp


def GoodAll (Q : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M → GoodFor Q χ

def BoundsII (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M →
    ‖gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChoiceOfModulusAndDiscriminant (n : ℕ) (x eps C : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 x eps) < q ∧ (q : ℝ) ≤ X1 x eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 x eps) < d ∧ (d : ℝ) ≤ X2 x eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1) ∧

  GoodAll (8 * X1 x eps) (psDir q) (8 * q * d) ∧
  GoodAll (8 * X1 x eps) (fun a => chi8 a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (chDir d) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chDir d a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a * psDir q a) (8 * q * d) ∧

  BoundsII x eps C (psDir q) (8 * q * d) ∧ BoundsII x eps C (chDir d) (8 * q * d) ∧
  BoundsII x eps C (fun a => chDir d a * psDir q a) (8 * q * d) ∧

  Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PairAt (Y eps : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 Y eps) < q ∧ (q : ℝ) ≤ X1 Y eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 Y eps) < d ∧ (d : ℝ) ≤ X2 Y eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1)

def PropTwoSixBoxHypothesis (D : D7) (x eps : ℝ) : Prop :=
  (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ BoxE D Y eps) ∧ Real.log (NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PropTwoSixThinScales (D : D7) (x eps c : ℝ) : Prop :=
  PropTwoSixBoxHypothesis D x eps →
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

section Family

variable {eps : ℝ}

def FamilySixthHypothesis (Fm : FamP eps) : Prop :=
  ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm6 (Fm.D x i) C1 c
def adm7F (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm7 (Fm.D x i) C
def ComplementTwoFamily (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm11 (Fm.D x i) C

def FamilyPropTwoSixCongruenceForm (Fm : FamP eps) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, PropTwoSixThinScales (Fm.D x i) x eps c

end Family

end Formalism.MainNotions.ShortIntervalPrimes

end
