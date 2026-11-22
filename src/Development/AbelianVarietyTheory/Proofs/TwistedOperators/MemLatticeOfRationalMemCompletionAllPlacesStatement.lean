module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places :
    ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsFullLattice D.host.E L →
      ∀ z : Fin S.rank → D.host.E,
        (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L :=
  GlobalTheory.RatLat.mem_of_mem_latV
