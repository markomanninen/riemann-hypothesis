module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  first | exact @GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | exact GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | (intros; apply GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one <;> assumption)
