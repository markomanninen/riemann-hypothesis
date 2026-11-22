module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePairCoordinates_transport_innerLattices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective (c.inn P.B.f) ∧ (∀ L, P.B.IsInner L ↔ S.IsInner S.f' S.es' (c.inn P.B.f L)) ∧ (∀ A, S.IsInner S.f' S.es' A → ∃ L, A = c.inn P.B.f L) ∧ ∀ L, c.lat (P.B.LamStd L) = S.stdLat S.f' S.es' (c.inn P.B.f L) := by
  first | exact @GlobalTheory.HL.CoordInnerSnd.transport | exact GlobalTheory.HL.CoordInnerSnd.transport | (intros; apply GlobalTheory.HL.CoordInnerSnd.transport <;> assumption)
