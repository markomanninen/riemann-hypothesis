module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

noncomputable section

namespace GlobalTheory.DetInv

open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta (epsTate epsEquiv epsPairing toO pairingO bQuot Realizes)

section Group

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)

theorem pairing_dual_bidual (t : G.Tate) (u : G.dual.Tate) :
    pairing G.dual O u (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t u :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing]
    have h1 : charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
        WithConv.toConv (t.pt n).toLinearMap :=
      (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)
    rw [h1]
    exact (apply_charElem u n _).symm

end Group

end GlobalTheory.DetInv
