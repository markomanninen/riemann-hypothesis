module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty

@[expose] public section

theorem UpperTheory.V.KernelIndexFullLattice.kernelIndexFullLattice_neBot :
    UpperTheory.V.KernelIndexFullLattice.NeBot :=
  @GroundTheory.Automorphic.CuspidalSpectrum.summandCuspForms_ne_bot
