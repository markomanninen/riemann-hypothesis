module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling
public import Development.EtaleCohomology.EtaleSheaves.GlueRelPfNat

@[expose] public section

open CategoryTheory GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.E4 LateralTheory.E.LeafGhostCut in
theorem UpperTheory.relativeCohomology_connecting_naturality :
    LateralTheory.E.NeighbourhoodKilling.ObsNat := by
  intro q _ U E U' E' f f' u e comm i m w
  obtain ⟨w, rfl⟩ := w.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst,
    Cochain.comp_assoc_of_second_is_zero_cochain]
