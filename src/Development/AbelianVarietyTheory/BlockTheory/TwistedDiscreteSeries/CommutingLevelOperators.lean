module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def typePl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def Differ (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c c' : Sys D) : Prop :=
  ∃ w d Rp, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb w d Rp ∧
    c w (dualLab d) ≠ c' w (dualLab d)

variable (t : T)

variable (P : LevelP R.Pg D.R.r ℂ)

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (PP : Pl D.host.E), R.C.P.Div k PP →
        ∀ (a : ℕ) (u : (kP PP)ˣ), (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 → (u : kP PP) = (a : kP PP) →
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            ((R.chi ((j : ℕ) + 1) PP u : ℂˣ) : ℂ) ∨
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            (((R.chi ((j : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ)

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

end
