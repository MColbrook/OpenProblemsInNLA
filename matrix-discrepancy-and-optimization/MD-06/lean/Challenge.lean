import «Definitions»

namespace MD06

/-! Independent Challenge specification.

This file records the complete MD-06 contract.  It intentionally does not
supply an implementation of `Semantics`: the finite uniform measure, torus
local-minimum predicate, derivatives and the even-subsequence limit must be
constructed and proved from pinned analysis libraries. -/

variable (S : Semantics)

#check MainClaim S
#check StrongClaim S
#check everyLocalMinimumSynchronized
#check hasStableNonsynchronizedCritical

/-- Statement-level conjunction retaining both the negative limit and the
strong high-probability stable critical-point conclusion. -/
def CompleteTarget : Prop := MainClaim S ∧ StrongClaim S

#check CompleteTarget S

end MD06
