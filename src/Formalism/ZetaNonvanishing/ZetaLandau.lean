module

public import Formalism.StatementU
public import Formalism.DefsOC
public import Formalism.ZetaNonvanishing.Assembly
public import Formalism.ZetaRealNonvanish
public import Formalism.ZetaNonvanishing.MellinSgen

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

def linZ (s : ℂ) : ℂ := -1 + (1 + (Real.eulerMascheroniConstant : ℂ)) * s

def nZ (s : ℂ) : ℂ := -(deriv riemannZeta₁ s / riemannZeta₁ s) + linZ s

def AZ (s : ℂ) : ℂ := -deriv riemannZeta₁ s + linZ s * riemannZeta₁ s

def HZ (ε C θ : ℝ) (x : ℝ) : ℝ := ε * Gz x + C * x ^ θ

end Formalism
