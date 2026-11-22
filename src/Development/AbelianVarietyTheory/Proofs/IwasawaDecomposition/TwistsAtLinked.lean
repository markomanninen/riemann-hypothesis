module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.CarriedPlMap
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.ColPins
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
