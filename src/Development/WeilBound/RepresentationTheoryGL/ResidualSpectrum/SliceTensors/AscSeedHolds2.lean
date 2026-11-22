module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedOfLocSub
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LocSubOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.FrobRecipHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.RestrictAtPointHolds

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem locSub_holds2 : LocSub := LsTop.locSub_of C3.Rap.restrictAtPoint_holds existsProj2 frobRecip_holds

theorem ascSeed_holds2 : AscSeed := ascSeed_of_locSub locSub_holds2

end PositivityTheory.Rg.Rs
