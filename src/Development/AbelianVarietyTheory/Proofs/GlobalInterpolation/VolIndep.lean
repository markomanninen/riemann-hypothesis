module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFundamentalDomainIffImageHA
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFundamentalDomainMap

@[expose] public section

namespace GlobalTheory.VolIndepClosed

theorem volIndep (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  (GlobalTheory.VolIndepCompare.volumeIndependence_iff D).1 (GlobalTheory.VolumeIndep.volumeIndependence D)

end GlobalTheory.VolIndepClosed
