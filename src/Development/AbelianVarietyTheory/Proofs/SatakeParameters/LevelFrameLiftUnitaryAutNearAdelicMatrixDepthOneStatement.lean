module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)) := by
  first | exact @GlobalTheory.FrameRat.nearAt_liftFr_smul | exact GlobalTheory.FrameRat.nearAt_liftFr_smul | (intros; apply GlobalTheory.FrameRat.nearAt_liftFr_smul <;> assumption)
