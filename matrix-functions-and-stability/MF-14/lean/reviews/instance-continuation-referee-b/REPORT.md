# MF-14 instance-alignment continuation — referee B

**Verdict: APPROVE this bounded source/evidence continuation for the repaired frozen packet.** The change preserves the original mathematical target and all 25 frozen contracts, and the actual local evidence resolves the previously observed elaborated-statement discrepancy. This is approval to proceed to the required real GitHub checks, not a claim that repaired Comparator/default-kernel/sandbox verification has already passed.

Reviewer: `/root/nr04_mf14_final_referee_b`, independent nonauthor AI agent, 19 September 2026. I authored no MF14 proof or repair and performed no Lean, Lake, Comparator, commit, push, rerun, promotion or completion-count change. This continuation builds on my separate full MF14-v1 mathematical review and preserves the separate blocking report for the two failed official runs at commit `fe4bbee26cc79f06587c803c5c902164c1e02e8e`.

## Exact scope and mathematical assessment

Reviewed packet: `final-review-packets/MF14-v2-instance-alignment`, snapshot SHA256 `10b1b576719a24d12d3a123a1180c2c89d26626a41367ef0abaf42001cb52892`. I rehashed all 101 packet files. Exactly one of the 87 Lean files changes from the approved v1 packet: `NLA/MF14Degree44/Mod3Certificate.lean`, now SHA256 `962a7033d3eaaba2c7121aafbf81543786d80eff58fb7bf89a8633df6147a78e`.

The entire delta is two explanatory comments and the line `attribute [-instance] ZMod.instField in` immediately before `integer_jacobian_mod3_inverse`. The `in` scopes the instance-selection change to that declaration. Removing those three added lines yields the earlier file byte for byte. The theorem header and proof body are unchanged; the frozen Challenge, Comparator configuration, definitions, other implementation declarations and all other packet files are unchanged.

The frozen contract still asserts an existential right inverse for the concrete 45 by 45 Jacobian matrix over `ZMod 3`. The change selects the commutative-ring instance already used when elaborating the reference declaration. It adds no assumption, axiom, alternate definition, trusted computation or replacement theorem. I inspected the pinned Mathlib ring and field instances: this is an algebra-instance elaboration alignment, not a change of the matrix domain or arithmetic. The proof still constructs the checked table inverse and uses the same checked matrix/table bridge.

The prior original-target assessment therefore carries forward: MF14's equality 42 is refuted via unconditional complex degree-44 coverage in the full 129-coefficient closure. The complete family, joint coefficient preservation, zero-parameter degeneration, actual derivative identity and modular witness remain intact. The continuation makes no exact degree-47 claim and does not broaden the earlier approved scope.

## Independently authenticated local evidence

Root's local evidence is `verification/MF14-repair095-local-20260919/LOCAL-REPLAY-AUDIT.json`, SHA256 `e514221a1ef727416004506ee71ad461aba5f8e110c91d3eb2c5be6909d5f408`. My independent `authenticate_continuation.py` checked its source bindings, compressed and uncompressed receipt hashes, recursively recorded reuse chains, actual successful fresh commands/logs, and dependency-output hashes. This did not execute any recorded command.

The actual recovery-095 run freshly compiled the changed `Mod3Certificate`, then `JacobianNonzero`, `JacobianIdentity`, `FinalClosure` and the publication-name `Solution`. Every command exited 0 with `--threads=1 --memory=4096`. The full aggregate source is unchanged; its actual log SHA256 is `4332f3f7259395d8785cf3877b763a6bb831f30ecd8a857ff131e6598b8a7336`. All 25 aggregate axiom reports and `#assert_trust kernel` assertions are present and use only the three permitted standard axioms. The pinned compiler binary was rehashed without execution and matches the recorded compiler hash.

I also read the complete diagnostic sources. The reference imports only `Challenge` and Lean; the solution diagnostic imports only `Solution` and Lean. For every one of the configured 25 theorem names, each uses `getConstInfo`, `reprStr info.type` and `reprStr info.levelParams`. Thus it records raw expressions including implicit instance arguments and universe parameter lists, rather than an abbreviated pretty-printed theorem statement. No expressions are rewritten or normalized by the diagnostic.

I authenticated the diagnostic source/log hashes and actual successful recovery-094/reference and recovery-095/solution command records, including their source-bound import outputs. Each actual log contains exactly 25 type blocks and 25 universe blocks with all configured names, and no truncation ellipses. The two complete logs are byte-identical: SHA256 `5ff7380dc81ef84138c68db3dfadd700672b52698b02183c99fd471723ea4f77`.

As a cross-check, I independently compared the pre-repair recovery-094 solution log to the same reference log. Only `integer_jacobian_mod3_inverse` differs. The old solution expression goes through `ZMod.instField` and `Nat.fact_prime_three`; the reference/repaired expression goes through `ZMod.commRing`. This agrees with the actual failed official Comparator's named contract and explains why identical literal source headers had not guaranteed the exact exported type. The other 24 raw declarations and universe lists already matched.

## Decision and limits

No blocking source or local-evidence finding remains within this continuation's scope. `AUDIT.json` records the independently checked counts and hashes; `MANIFEST.json` binds this report, the exact old/new snapshots, all local evidence, diagnostic source/log copies and the prior source/failure reports. The diagnostic and compilation are explicitly local macOS evidence. They do not invoke Comparator, replay the solution in its fresh Linux kernel environment, or establish sandbox acceptance.

The historical failed-run report and directory remain unchanged. The repaired publication commit must receive successful actual GitHub checks and a separate runtime evidence audit before promotion or counting. This continuation approves the exact repaired packet above and no later source change.
