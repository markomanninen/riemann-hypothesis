module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Side (D : D7) (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E x)) =
    D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E x))

def SitsAt (D : D7) (σ : D.what₂.LL →+* ℂ) (τ τ' : D.what₂.Tau) : Prop :=
  ∃ t : D.host.E →+* D.what₂.LL, D.what₂.embLL.comp t = tauE D τ ∧ σ.comp t = tauE D τ'

def IsConjPar (D : D7) (j : ℕ) (σ : D.what₂.LL →+* ℂ) (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ', ∃ τ, SitsAt D σ τ τ' ∧ S τ' = parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)) τ

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def IsCover (V : HSp D) {G0 : Type} [Group G0] (Lift : G0 → GA D V → Prop) : Prop :=
  (∀ κ, κ ∈ levSet V 1 ↔ ∃ g, Lift g κ) ∧ (∀ g, ∃ κ, Lift g κ) ∧
    (∀ g g' κ, Lift g κ → Lift g' κ → g = g') ∧
    (∀ g g' κ κ', Lift g κ → Lift g' κ' → Lift (g * g') (κ * κ')) ∧
    ∀ κ, Lift 1 κ ↔ κ ∈ levSet V (D.host.g 0 * D.host.g 1)

variable (T : CoreJ D) (j : ℕ)

def rdK (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (c : (T.U j s).Comp → ℂ) : T.R j →ₛₗ[s] (GA D (T.V j s) → ℂ) :=
  ((lieFac (T.Q.Dw j) (xiR D) (wtA w) : ℂ) •
    adel (T.V j s) (T.dict j s) (muPin (T.V j s) (T.dict j s) (T.mu j s) c)).comp (rdU (T.U j s))

variable [Algebra T.Q.c.F D.what₂.LL]

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
