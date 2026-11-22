module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

namespace GlobalTheory

theorem siegelKlingenDeligneRibet_of_both :
    GlobalTheory.Published.SiegelKlingen → GlobalTheory.Published.DeligneRibet → GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  fun a b => ⟨a, b⟩

end GlobalTheory
