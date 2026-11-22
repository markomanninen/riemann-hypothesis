module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartOneOfSemistableReductionPadicPolarized
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Moduli

theorem _root_.GlobalTheory.Moduli.jointExistence_and_moduliScheme : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab :=
  ⟨_root_.GlobalTheory.partI_of_semistableReduction _root_.GlobalTheory.SS.semistableReductionSt,
    _root_.GlobalTheory.Moduli.moduli_scheme_exists⟩

end GlobalTheory.Moduli
