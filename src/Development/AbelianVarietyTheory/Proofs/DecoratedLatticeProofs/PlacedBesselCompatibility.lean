module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselAwayPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalComponentData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentity

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

theorem GlobalTheory.MiTop.levFn_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {LL : Type} [CommRing LL] (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E LL n) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.L2.DIV.lev hc J β L) (hy : y ∈ Formalism.L2.DIV.lev hc J β L) :
    Formalism.L2.DIV.levFn β L (x * y * x⁻¹) = Formalism.L2.DIV.levFn β L y := by
  have e := congrArg (Formalism.L2.DIV.levChar hc J β L)
    (show (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : Formalism.L2.DIV.lev hc J β L)⁻¹ : Formalism.L2.DIV.lev hc J β L) =
      ⟨x * y * x⁻¹, _⟩ from rfl)
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at e
  exact e.symm

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop
