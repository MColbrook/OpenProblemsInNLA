import LeanFormalizations.NumberTheory.Transcendence.PiTranscendental

/-!
The classical input used at the end of manuscript Section 5. Its external
proof, attribution, license and immutable upstream hashes are retained in
`vendor/gotrevor-pi/`. This declaration must be kernel checked together
with that dependency; a literature citation is not an axiom.
-/

namespace MF21Restart

theorem pi_transcendental : Transcendental ℚ Real.pi :=
  LeanFormalizations.Transcendence.transcendental_pi_axiomClean

#print axioms pi_transcendental

end MF21Restart
