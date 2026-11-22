module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKOfStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDetLiftLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTwGen
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Top.Bl.WitSK

def of_sigma_eq {α : Type*} {β : α → Type*} {a b : Σ x, β x} (h : a = b) (P : ∀ x, β x → Sort*) (hb : P b.1 b.2) :
    P a.1 a.2 := by
  subst h; exact hb

end GlobalTheory.Mem.Top.Bl.WitSK

