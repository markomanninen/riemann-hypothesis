module

public import Formalism.SmithDeterminants.StatementGram
public import Formalism.SmithDeterminants.DivisibilityChains.SmithExists

@[expose] public section

namespace Formalism.A

theorem smithExists : SmithExists := smith_form_exists

end Formalism.A
