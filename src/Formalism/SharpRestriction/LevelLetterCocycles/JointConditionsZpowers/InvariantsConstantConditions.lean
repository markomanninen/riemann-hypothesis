module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLen
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.KsMono
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section H0

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def tTwoLocalLattice {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)))) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
  { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)), cont := hc, L := L2 }

end H0

end Formalism.MainNotions.N
