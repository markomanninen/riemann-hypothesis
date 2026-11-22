module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OAf (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def finR (V : HSp D) {r : ℕ} (hr : V.rank = r) : GA D V →* GL (Fin r) (EAf D) :=
  (Units.map (Matrix.reindexRingEquiv (EAf D) (finCongr hr)).toRingHom.toMonoidHom).comp (finE V)

def IsLatBasis (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) : Prop :=
  ∀ z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E, z ∈ latHat V ↔
    ∀ i, (Units.val (β⁻¹ : GL (Fin r) (EAf D))).mulVec
      (fun a => swapAE D (z (Fin.cast hr.symm a))) i ∈ OAf D

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
