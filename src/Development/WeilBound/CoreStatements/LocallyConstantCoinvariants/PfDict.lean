module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs

@[expose] public section

namespace PositivityTheory.KCo

theorem dictionary_extended : DictX := dictX_of model_existence cyclicity adjoint_statement section_statement action_uniqueness

theorem dictionary_statement : DictSt := dictSt_of dictionary_extended section_statement

end PositivityTheory.KCo
