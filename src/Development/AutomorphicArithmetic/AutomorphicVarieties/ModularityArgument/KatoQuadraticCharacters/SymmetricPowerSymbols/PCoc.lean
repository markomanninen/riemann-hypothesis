module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsBis

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.pCoc :
    UpperTheory.V.Z.Kato.Sym.PCoc := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw
  exact ⟨PC.eqv Ω ε X m c d M hm hc hd hc6 hd6 hL t w ht hw,
    PC.coc Ω ε X m c d M hm hc hd hc6 hd6 hL t w ht hw,
    PC.loc Ω ε X m c d M hm hc hd hc6 hd6 hL t w ht hw⟩
