module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OrderValuation
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChangeStatement

@[expose] public section

noncomputable section

namespace GlobalTheory.TransferCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.PjFree (valSet algCls cusp Unf regular₂ trivSet isVal_valSet DomWt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36 (algVal allVal ordVal Comb LeastLe Transfer TransferAt TransferInt TransferComb TransferLeast
  ordVal_smul)

section Order

end Order

section Approx

variable {K : Type} [Field K] [NumberField K]

end Approx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Objects

variable (Xo c)

variable {Xo c}

end Objects

section Joint

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

variable {Xo c U}

variable (Xo c)

theorem evalWD_framed : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_fr (frChartF_of (GlobalTheory.T.chartCoverF_of_sectionBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c))

theorem frBC_framed : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem allTest_framed : AllTest Xo c :=
  GlobalTheory.T.framedPoint_reduced_from_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c



variable (U)

end Joint

end GlobalTheory.TransferCompare
