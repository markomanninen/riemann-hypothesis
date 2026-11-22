module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ArthurClozelStrongSupp : Prop := StrongBC lbc

end GlobalTheory.Published

end
