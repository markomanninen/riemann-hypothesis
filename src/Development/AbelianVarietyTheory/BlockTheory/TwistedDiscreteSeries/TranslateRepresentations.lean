module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

def IsTransRep {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r)
    (M : HMod (Bridge.Gf V → W)) (ρ : Representation ℂ G M.H) : Prop :=
  ∀ g x, IsTranslate V β L (eG g) (M.e x) (M.e (ρ g x))

variable {V β L}

end Space

def Commutes {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
