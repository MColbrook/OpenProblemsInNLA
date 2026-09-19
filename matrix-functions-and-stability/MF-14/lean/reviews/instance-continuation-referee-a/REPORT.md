# MF14 nonauthor continuation review

**Verdict: APPROVE the repaired frozen source.** No blocking mathematical,
scope, axiom, or source-quality finding was identified in this continuation.
This approval does not assert a successful repaired Linux Comparator run.

Reviewer: `/root/nr04_mf14_final_referee_a`, independent AI nonauthor of MF14.
I authored no MF14 proof or repair, ran no Lean/compiler or Comparator, and
did not edit either frozen packet or the publication. My separate MI27
authorship does not overlap this MF14 review. This report continues my full
MF14-v1 review, REPORT SHA256
`9487b2edcaa41f6f037f2b3277c2802c24770f21167590b0de376494560f7715`.

The repaired packet is `MF14-v2-instance-alignment`, REVIEW-SNAPSHOT SHA256
`10b1b576719a24d12d3a123a1180c2c89d26626a41367ef0abaf42001cb52892`.
I independently verified all 101 registered file hashes in each packet and
compared all 87 Lean files. Only `NLA/MF14Degree44/Mod3Certificate.lean`
changes, from SHA `bf12a3b817de8c2abeeb15a53412884f9ebeb9d2f9712573d7ce102aac60638a`
to `962a7033d3eaaba2c7121aafbf81543786d80eff58fb7bf89a8633df6147a78e`.
The exact delta is two comments followed by the declaration-scoped command
`attribute [-instance] ZMod.instField in` before
`integer_jacobian_mod3_inverse`. The frozen Challenge, definitions,
certificate entries, theorem header text, proof body, all downstream proof
sources, and original mathematical target are unchanged.

The repair selects the frozen commutative-ring instance while elaborating
this one declaration. It adds no assumption, substitute matrix, axiom, or
new trust mechanism. I inspected the pinned Mathlib ZMod commutative-ring
and prime-field definitions, the complete changed module, and the immediate
determinant transfer in JacobianNonzero. The right inverse is still the
same checked 45-by-45 matrix modulo three; the actual integer Jacobian and
its determinant transport remain unchanged. Consequently the earlier full
review of unconditional degree-44 coverage in all 129 coefficients remains
applicable. The original answer remains that the asserted equality 42 is
false; this does not assert an exact value 47.

I inspected the retained original fork run 35431937168 and upstream run
35431941636 metadata and Comparator logs. Both built Lean successfully and
then failed the statement match for `integer_jacobian_mod3_inverse`, with
exit status 1. This was a real failed mechanical gate despite identical
surface header text. The new local diagnostic directly prints `info.type`
and `info.levelParams` from the separately imported Challenge and Solution.
I checked its source, contract list, successful command receipts, and raw
outputs: all 25 types and universe parameter lists are byte-identical,
322506 bytes, SHA256
`5ff7380dc81ef84138c68db3dfadd700672b52698b02183c99fd471723ea4f77`.
The repaired D44-08d expression explicitly uses `ZMod.commRing`.

Actual root-controlled local recovery095 compiled Mod3Certificate (11.02s),
JacobianNonzero (4.09s), JacobianIdentity (6.47s), FinalClosure (4.82s), and
Solution (4.66s), each with exit code 0, one thread and 4096 MiB. I inspected
their logs and source-bound receipts. All 25 aggregate axiom reports use
only `propext`, `Classical.choice`, and `Quot.sound`; the successful aggregate
contains all 25 kernel trust assertions. I additionally authenticated the
replay audit (SHA `e514221a1ef727416004506ee71ad461aba5f8e110c91d3eb2c5be6909d5f408`),
56 compressed original receipts, 86 successful module origins, 807 reuse
links, retained log hashes, and dependency-output links. The accompanying
Python audit performs only static source/log checks; it is not proof execution.

Scope limitations: this is a bounded continuation, not a second reread of
every unchanged proof. No repaired Linux run, final publication metadata,
or new novelty search was reviewed. The original failed Linux runs are not
success evidence for the repair. The repaired final Comparator/kernel/
sandbox gate remains separate. No completed Lean verification or new
mathematical-resolution count is incremented by this report.
