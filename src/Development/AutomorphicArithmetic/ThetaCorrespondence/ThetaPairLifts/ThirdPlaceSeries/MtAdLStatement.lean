module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtAdL

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel :
    ∀ {hL : UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre}
      {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P}
      (L : LocAll (lay0 (Dof x))) (l : StrictHenselianAcyclicLevel hL x)
      {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0),
      YRel L Y → ∃ ad : MtAd Y (localMultiplicityFamily L l), ad.PV = psiVectorLocal L l :=
  @GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel
end
