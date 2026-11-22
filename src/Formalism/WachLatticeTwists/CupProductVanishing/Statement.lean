module

public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Defs

variable {O G VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT']

def pairF (D : LatData O G VT VT') : H1 D.ρT →ₗ[O] H1 D.ρT' →ₗ[O] FractionRing O :=
  (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT').compr₂ D.invF

def withInv (D : LatData O G VT VT') (inv : H2 (twist D.ε (KO O)) →ₗ[O] KO O)
    (invF : H2 (twist D.ε (FractionRing O)) →ₗ[O] FractionRing O) : LatData O G VT VT' :=
  { D with inv := inv, invF := invF }

end Defs

end Formalism.RepresentationBoundsCohomology.T2
