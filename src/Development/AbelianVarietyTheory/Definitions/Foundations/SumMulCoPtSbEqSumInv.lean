module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu

@[expose] public section

noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def coPtSb (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d a b : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) b s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a (d * b) s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) *
        GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) (d * b) s

theorem coPtSb_one (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) :
    coPtSb N p m k ψ c d x 1 s = GlobalTheory.KummerEisensteinGalois.coPtS N p m k ψ c d x s := by
  simp [coPtSb, GlobalTheory.KummerEisensteinGalois.coPtS]

def chiAvg (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s


omit [CharZero K] in
theorem ffMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' : ℤ} (h : a ≡ a' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a = GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ a [ZMOD N] ↔ z ≡ a' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.ffMu, h']


omit [CharZero K] in
theorem eeMu_congr (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) {b b' : ℤ} (h : b ≡ b' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b = GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ b [ZMOD N] ↔ z ≡ b' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.eeMu, h']


omit [CharZero K] in
theorem coPtMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b = GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a' b' := by
  simp only [GlobalTheory.KummerEisensteinGalois.coPtMu, ffMu_congr N p m k ψ ha, eeMu_congr N p m ψ hb]


omit [CharZero K] in
theorem coPtSb_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : coPtSb N p m k ψ c d a b = coPtSb N p m k ψ c d a' b' := by
  funext s
  simp only [coPtSb, coPtMu_congr N p m k ψ ha hb, coPtMu_congr N p m k ψ (ha.mul_left c) hb,
    coPtMu_congr N p m k ψ ha (hb.mul_left d), coPtMu_congr N p m k ψ (ha.mul_left c) (hb.mul_left d)]






end GlobalTheory.LambdaValuationPowers
