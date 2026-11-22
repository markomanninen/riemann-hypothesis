module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import GroundTheory.GlobalFields.Adele.Compact
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Lit

section Comp

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]


omit [IsTotallyReal E] in
private def zf (y : Af E) : Ad E := ((0, y) : InfiniteAdeleRing E × Af E)


private theorem split (x : Ad E) : x = TR.sInf E (TR.pInf E x) + zf (pFin E x) :=
  Prod.ext (((TR.infEq E).apply_symm_apply _).symm.trans (add_zero _).symm) (zero_add _).symm


variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

end Comp

section Pull

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}



variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs


end Pull

end UpperTheory.V.Lit
