module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  ∑ u ∈ c.support, c u • heisO ψ S T u f

def IsFinComb {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, u.map (infPart D) = 0

def biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => comb ψ S A' c' (C u') v) u

structure IsBiVac (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  left : ∀ v, IsThetaFunO ψ A S (fun u => C u v) ∧ IsLatVac (heisO ψ A S) (latO A S LA LS fun _ => True) fun u => C u v
  right : ∀ u, IsThetaFunO ψ S A' (C u) ∧ IsLatVac (heisO ψ S A') (latO S A' LS LA' fun _ => True) (C u)

def JointSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

def biLift {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S A' → ℂ) (h₂ : GA D A') : ℂ :=
  ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 ∂vA.μ) ∂vS.μ

def HasCen (A : HSp D) (χ : GA D A → ℂ) (φ : GA D A → ℂ) : Prop :=
  ∀ z ∈ GinfC A, z ∈ Subgroup.center (GA D A) → ∀ h, φ (h * z) = χ z * φ h

def InCell {V : HSp D} (R : Subgroup (GA D V)) (t : GA D V) (J : Set (GA D V)) (h : GA D V) : Prop :=
  ∃ r ∈ R, ∃ a ∈ GinfC V, ∃ k ∈ J, h = r * a * t * k

structure DefSp (V : HSp D) where
  s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  vol : Vol V

structure DefSp.Is {V : HSp D} (x : DefSp V) : Prop where
  sig : V.SigOK
  cpt : CoCpt V
  cart : ∀ τ, IsCartanInv (gramAt D V τ) (x.s τ)
  pm : ∀ τ, x.s τ = 1 ∨ x.s τ = -1
  onb : ∀ τ, ∃ p, IsONBasis (gramAt D V τ) (x.s τ) (x.B τ) p
  sd : IsSelfDualC V x.L

structure KerDat (S T : HSp D) where
  om : Om S T
  vac : WO S T → ℂ
  c : WO S T →₀ ℂ

structure KerDat.Is (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T) :
    Prop where
  weil : ∃ χS χT, IsWeilDatumO ψ S T χS χT k.om
  vac : IsVacO ψ θ S T x.s y.s x.L y.L k.vac
  fin : IsFinComb k.c

def KerDat.pt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) : WO S T → ℂ :=
  pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T k.c k.vac) P

def KerDat.lift (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) (φ : GA D S → ℂ) : GA D T → ℂ :=
  liftT k.om x.vol.μ x.vol.𝓕 φ (k.pt ψ θ x y P)

def FockReduce (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → JointSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

structure BesAt (V A : HSp D) (ρ : ℕ) where
  V₀ : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vN : VolN d

@[reducible] def BesAt.lev {V A : HSp D} {ρ : ℕ} (b : BesAt V A ρ) (vA : Vol A) : BesLev D ρ :=
  ⟨V, b.V₀, A, b.L, b.d, b.o, b.ζ, b.line, b.cpt, vA, b.vN⟩

structure JacAt (W W₀ : HSp D) (ρ : ℕ) where
  d : HypDec W W₀ ρ
  cpt : CoCpt W₀
  vN : VolN d

@[reducible] def JacAt.lev {W W₀ : HSp D} {ρ : ℕ} (b : JacAt W W₀ ρ) (v0 : Vol W₀) : JacLev D ρ :=
  ⟨W, W₀, b.d, b.cpt, v0, b.vN⟩

open GlobalTheory.ChainOnto (Com PiLocalization₂)

structure StAt (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

@[reducible] def StAt.st {V : HSp D} (a : StAt V) : PiLocalization₂ D := ⟨V, a.par, a.M, a.Λ, a.β, a.L, a.ν, a.fd⟩

structure Geo (D : D7) where
  c : Com D
  bot : StAt (D.sp.Y 0)
  mid : ℕ → PiLocalization₂ D
  top : StAt D.sp.X'

def Geo.st (g : Geo D) : ℕ → PiLocalization₂ D
  | 0 => g.bot.st
  | j + 1 => g.mid j

abbrev Col (D : D7) (u : D.what₂.Word) (j : ℕ) : Type := (D.mem u).C.cls j → (D.mem u).C.Y j → ℂ

theorem idx_step {j σ m : ℕ} (h : j + 2 * (σ + 1) + 2 = m) : j + 1 + 1 + 2 * σ + 2 = m := by omega


set_option maxHeartbeats 1000000 in
structure Dat (D : D7) (u : D.what₂.Word) extends Geo D where

  p : ∀ j, GlobalTheory.ChainOnto.Step c (toGeo.st j) (toGeo.st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step c (toGeo.st (j + 1)) top.st

  t : ∀ j, GA D (toGeo.st j).V

  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))

  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (toGeo.st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (toGeo.st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF c.ψ ((bes j ρ h).lev (x j).vol) ((jac j ρ h).lev (x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB c.ψ ((jac j (σ + 1) h).lev (x (j + 1)).vol) ((bes (j + 1 + 1) σ (idx_step h)).lev (x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz

  Ram : ∀ j, Submodule ℂ (Col D u j)
  S : ∀ j, Col D u j →ₗ[ℂ] Col D u j
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ

  eT : (D.mem u).P.Mt → top.st.CC c

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

abbrev B (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : BesLev D ρ := (d.bes j ρ h).lev (d.x j).vol

abbrev lev (j : ℕ) : Set (GA D (d.st j).V) := levS (d.st j).V (d.st j).β (d.st j).L

structure Base : Prop where
  com : d.c.Is
  st : ∀ j, j < D.R.m → (d.st j).Is d.c j
  top : d.top.st.Is d.c D.R.m
  p : ∀ j, j + 1 < D.R.m → (d.p j).Is (j + 1)
  pT : ∀ j h, (d.pT j h).Is D.R.m
  t : ∀ j, d.t j ∈ GfC (d.st j).V
  x : ∀ j, j ≤ D.R.m → (d.x j).Is
  k : ∀ j, j < D.R.m → (d.k j).Is d.c.ψ d.c.θ (d.x j) (d.x (j + 1))
  sBF : ∀ j ρ h, (d.sBF j ρ h).om = (d.p j).ω ∧ (d.sBF j ρ h).vW.μ = (d.st (j + 1)).ν ∧ (d.sBF j ρ h).vW.𝓕 = (d.st (j + 1)).fd
  sFB : ∀ j σ h, (d.sFB j σ h).om = (d.p (j + 1)).ω ∧ (d.sFB j σ h).vW.μ = (d.st (j + 1 + 1)).ν ∧
    (d.sFB j σ h).vW.𝓕 = (d.st (j + 1 + 1)).fd

end Dat

end GlobalTheory.SeeSaw

end
