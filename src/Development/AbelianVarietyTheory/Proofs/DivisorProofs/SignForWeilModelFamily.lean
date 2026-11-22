module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignExists
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionDeterminantRoot

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DatumFourier

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.DatumFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem isThPVecOf_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT Pg Q ξ ξ' f₀ f}
    (hQ : Q = ∅) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f := by
  subst hQ
  have e : ∀ y, omegaQ (a := T.rank) (b := S.rank) ∅ T.rank ξ' (-1) y = omegaQ ∅ T.rank ξ (-1) y := fun y => by
    simp [omegaQ]
  unfold IsThPVecOf at h ⊢
  simp only [e]
  exact h


end GlobalTheory.GalOne

end
