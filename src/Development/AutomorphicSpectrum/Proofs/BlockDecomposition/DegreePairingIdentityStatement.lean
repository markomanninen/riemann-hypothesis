module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_pairing_identity : WedgeF → WedgeI → MulF → MulI → PairF → PairI → SzFin → FinSupp → LogAbsBasic → ConjPlaces → DegBasisG → Radical → DegPairing := by
  first | exact @GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of | exact GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of | (intros; apply GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of <;> assumption)
