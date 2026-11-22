module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def CombAt (P : Pl D → Prop) {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, MxAt P u

def extS {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) (c : WO A T →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resS T).symm (u, 0)

def extT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c : WO S A →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resT S).symm (u, 0)

def kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w : WO S L'') : WO L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)

def lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) : WO A S → WO S X → ℂ :=
  fun u => o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))

def BiVacAt (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A') (P : Pl D → Prop)
    (C : WO A S → WO S A' → ℂ) : Prop :=
  (∀ v, Vac ψ A S LA LS P fun u => C u v) ∧ ∀ u, Vac ψ S A' LS LA' P (C u)

variable {u : D.what₂.Word}

def offS (d : Dat D u) (v : Pl D) : Prop := v ∉ d.c.S

def onS (d : Dat D u) (v : Pl D) : Prop := v ∈ d.c.S

def xiBF (d : Dat D u) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (a : GA D (d.st (j + 1)).V) : WO (d.bes j ρ h).V₀ (D.sp.X (j + 1)) → ℂ :=
  flatBF (d.sBF j ρ h) ((d.p j).ω (d.t j, a * d.t (j + 1)) ((d.p j).pt P₁))

def xiFB (d : Dat D u) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (P₂ : Formalism.IndefR.Links.PolF D (d.st (j + 1 + 1)).V.rank (d.st (j + 1)).V.rank) (a : GA D (d.st (j + 1)).V)
    (a' : GA D (d.st (j + 1 + 1)).V) : WO (D.sp.X (j + 1)) (d.bes (j + 1 + 1) σ (idx_step h)).V₀ → ℂ :=
  flatFB (d.sFB j σ h) ((d.p (j + 1)).ω (a * d.t (j + 1), a' * d.t (j + 1 + 1)) ((d.p (j + 1)).pt P₂))

def xiTop (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) : WO (D.sp.X (j + 1)) D.sp.X' → ℂ :=
  fun w => (d.pT j h).ω (d.t (j + 1), 1) ((d.pT j h).pt P₂) ((d.jac j 0 h).d.ext0 D.sp.X' w)

structure OffDat (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where

  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (d.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (d.st j).V

  M : ∀ j ρ h, Lat (d.bes j ρ h).V₀

  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E

  ζ₀ : Fin d.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {d : Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffDat d k ι)

namespace OffDat

def atT (v : Pl D) : Prop := ∃ i, v = (o.p i).v

def pair (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : PairDat o.p (D.sp.X j) (d.bes j ρ h).V₀ (Fin (D.sp.X j).rank) :=
  ⟨o.β j, o.β₀ j ρ h, o.Q j⟩

def mid (j : ℕ) : MidDat o.p (D.sp.X j) (Fin (D.sp.X j).rank) := ⟨o.β j, o.Q j⟩

def dbl (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) :
    DblLat (d.B j (σ + 1) h) ((d.jac j (σ + 1) h).lev (d.x (j + 1)).vol) (d.B (j + 1 + 1) σ (idx_step h)) :=
  ⟨o.L j, o.M j (σ + 1) h, o.L (j + 1), (d.x (j + 1)).L, o.L (j + 1 + 1), o.M (j + 1 + 1) σ (idx_step h)⟩

end OffDat

structure PinOff : Prop where

  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  inj : Function.Injective fun i => (o.p i).v
  off : ∀ i, offS d (o.p i).v

  char : ∀ i, (o.p i).IsChar d.c.ψ (o.χ i) ∧ (o.p i).UnitAA

  moves : ∀ j, j < D.R.m → IsSelfDualC (d.st j).V (o.L j) ∧ ∀ P, Moves (d.st j).V (d.t j) (d.st j).Λ (o.L j) P

  latT : ∀ j, j ≤ D.R.m → ∀ i, (o.β j i).IsLat (d.x j).L (o.Q j i).lat

  shape : ∀ j σ h, DblShape (d.sBF j (σ + 1) h) (d.sFB j σ h) (o.dbl j σ h) (offS d) o.q (o.pair j (σ + 1) h) (o.mid (j + 1))
    (o.pair (j + 1 + 1) σ (idx_step h))

  goodLast : ∀ j h v, offS d v → GoodBF d.c.ψ (d.B j 0 h) ((d.jac j 0 h).lev (d.x (j + 1)).vol) (o.L j) (o.M j 0 h) (o.L (j + 1))
    (d.x (j + 1)).L v ∧ UnrAt (d.sBF j 0 h) v

  gluedLast : ∀ j h i, GluedCore (d.B j 0 h) (o.M j 0 h) o.q (o.β j i) (o.β₀ j 0 h i) (o.Q j i)

  core : ∀ j ρ h v, offS d v → ¬ o.atT v → ∃ LL, IsSelfDualC (d.bes j ρ h).L LL ∧ OrthAt (d.bes j ρ h).o (o.M j ρ h) (d.x j).L LL v

  parts : ∀ j, j < D.R.m → CombAt o.atT (o.cT j) ∧ CombAt (onS d) (o.cG j) ∧
    ∀ f, comb d.c.ψ _ _ (d.k j).c f = comb d.c.ψ _ _ (o.cG j) (comb d.c.ψ _ _ (o.cT j) f)

  rep : ∀ j, j < D.R.m → ∀ f, Vac d.c.ψ _ _ (d.x j).L (d.x (j + 1)).L o.atT f →
    OverAll d.c.ψ (o.β j) (o.β (j + 1)) (d.x j).L (d.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb d.c.ψ _ _ (o.cT j) f)

  unrK : ∀ j, j < D.R.m → ∃ χS χT, IsWeilDatumO d.c.ψ _ _ χS χT (d.k j).om ∧
    ∀ i, CharUnramAt D χS (o.p i).v ∧ CharUnramAt D χT (o.p i).v

  weil : ∀ j σ h, ∃ (χA χA' χz : (AE D)ˣ →* Circle) (omz : Om (d.bes j (σ + 1) h).L (D.sp.X (j + 1)))
    (omz' : Om (D.sp.X (j + 1)) (d.bes (j + 1 + 1) σ (idx_step h)).L),
    (d.sBF j (σ + 1) h).χV = χA * χz ∧ (d.sFB j σ h).χW = χA' * χz ∧
    IsWeilDatumO d.c.ψ _ _ χA (d.sBF j (σ + 1) h).χW (d.k j).om ∧ IsWeilDatumO d.c.ψ _ _ χz (d.sBF j (σ + 1) h).χW omz ∧
    IsWeilDatumO d.c.ψ _ _ (d.sFB j σ h).χV χA' (d.k (j + 1)).om ∧ IsWeilDatumO d.c.ψ _ _ (d.sFB j σ h).χV χz omz'

  weilLast : ∀ j h, ∃ (χA χz χS' χT : (AE D)ˣ →* Circle) (omz : Om (d.bes j 0 h).L (D.sp.X (j + 1)))
    (omT : Om (D.sp.X (j + 1)) D.sp.X') (omz'' : Om (D.sp.X (j + 1)) d.Lz),
    (d.sBF j 0 h).χV = χA * χz ∧ IsWeilDatumO d.c.ψ _ _ χA (d.sBF j 0 h).χW (d.k j).om ∧
    IsWeilDatumO d.c.ψ _ _ χz (d.sBF j 0 h).χW omz ∧ IsWeilDatumO d.c.ψ _ _ χS' (χT * χz⁻¹) (d.k (j + 1)).om ∧
    IsWeilDatumO d.c.ψ _ _ χS' χT omT ∧ IsWeilDatumO d.c.ψ _ _ χS' χT (d.pT j h).ω ∧ IsWeilDatumO d.c.ψ _ _ χS' χz⁻¹ omz'' ∧
    ∀ i, CharUnramAt D χS' (o.p i).v ∧ CharUnramAt D χT (o.p i).v

  line : IsLineVec d.Lz o.ζ₀

  tau : ∀ j h, (o.τ j h)ᴴ ⬝ ((d.bes j 0 h).L.gram ⬝ o.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • d.Lz.gram ∧
    ∃ lam : D.host.E, o.τ j h *ᵥ o.ζ₀ = lam • (d.bes j 0 h).ζ ∧ ∀ i, valuation k ((o.p i).pr (incA D lam)) = 1

  top : ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, offS d v → ¬ o.atT v → ∃ (LL : Lat (d.bes j 0 h).L) (LZ : Lat d.Lz),
    IsSelfDualC _ LL ∧ IsSelfDualC _ LZ ∧ OrthAt (d.bes j 0 h).o (o.M j 0 h) (d.x j).L LL v ∧
    OrthAt (d.oT (j + 1 + 1) h) (d.x (j + 1 + 1)).L d.top.Λ LZ v ∧
    ∀ w ∈ latO (D.sp.X (j + 1)) d.Lz ((d.x (j + 1)).L : Set _) (LZ : Set _) (· = v),
      kap (o.τ j h) (D.sp.X (j + 1)) w ∈ latO (d.bes j 0 h).L (D.sp.X (j + 1)) (LL : Set _) ((d.x (j + 1)).L : Set _) (· = v)

  topT : ∀ n (h : n = D.R.m) i, IsSumFrame (d.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i) ∧
    ∃ (Λ : Submodule 𝒪[k] (Fin D.sp.X'.rank → k)) (s : 𝓀[k]ˣ), (o.γ i).IsLat d.top.Λ Λ ∧
      (∀ y, y ∈ (o.Q n i).ker ↔ ((o.γ₀ n h i).b' * (o.β n i).b) *ᵥ y ∈ lastKer Λ) ∧
      (o.Q n i).HasVal (((o.β n i).b' * (o.γ₀ n h i).b) *ᵥ (o.q.inv • avec k (Fin D.sp.X'.rank) 1 1)) s

def IsS (j : ℕ) (ε : ι → 𝓀[k]ˣ) : Prop :=
  ∀ ψ ∈ d.Ram j, d.S j ψ ∈ d.Ram j ∧ ∀ y, d.rd j (d.S j ψ) y =
    o.I.foldr (fun i φ => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε i) φ) (d.rd j ψ y)

theorem rank_pos_of_le (D : D7) {j : ℕ} (h : j ≤ D.R.m) : 0 < (D.sp.X j).rank := by
  rw [D.sp.X_rank j h]
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)

variable {o} {Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)}

namespace OffTest

theorem combAt_single_zero (P : Pl D → Prop) {S T : HSp D} (c : ℂ) : CombAt P (Finsupp.single (0 : WO S T) c) := by
  intro u hu
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
  intro i j
  exact Submodule.zero_mem _

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  simp [comb]
  exact GlobalTheory.MixPer.heisO_zero ψ S T f

end OffTest

end GlobalTheory.FinPl

end
