module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalRingCardinality.DataTies
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Volume

variable {D : D7}

def volBox (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (B : D.what₂.Tau → Set (UpqT P Q)) : Set (GA D V) :=
  {h | ∃ k ∈ KsphC V ∅, ∃ g ∈ GinfC V, h = k * g ∧
    ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) g}

def IsProductForm (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (μ : Measure (GA D V)) : Prop :=
  ∀ B : D.what₂.Tau → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) →
    μ (volBox θ V A B) = ∏ ρ, D.cd.cd P Q (B ρ)

variable (D)

end Volume

section Ideles

variable (D : D7)

abbrev AE : Type := AF D.host.F ⊗[D.host.F] D.host.E

abbrev IdE : Type := (AE D)ˣ

abbrev IdF : Type := (AF D.host.F)ˣ

def resF : IdF D →* IdE D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    AF D.host.F →+* AF D.host.F ⊗[D.host.F] D.host.E).toMonoidHom

def ratF : D.host.Fˣ →* IdF D := Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom

def conjId : IdE D →* IdE D := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def normId : IdE D →* IdE D := MonoidHom.id (IdE D) * conjId D

end Ideles

section Hecke

variable (D : D7)

def normGroup : Subgroup (IdF D) := (ratF D).range ⊔ (normId D).range.comap (resF D)


variable {D}


variable (D)

end Hecke

section Witt

variable {D : D7}

variable (D)

end Witt

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

end
