# Final MF-21 publication metadata review

**Verdict: APPROVE. No material contradiction found.**

Reviewer: Codex agent `/root/mf21_final_statement_referee`, 21 September 2026 UTC. Scope: project `README.md`, `VERIFICATION.md`, and `formalization.yaml` at publication commit `fe2183e9b570322d7c1f64bba3480460082af8d3`, compared with actual current local evidence and the source-copy receipt. I ran no compiler, queried no GitHub updates, and edited no project files. This report is outside the proof project.

The documents accurately describe **10 successful recompilations, 115 validated reused outputs, and 386 actual axiom reports**, rather than another 125-invocation build. I independently checked the phase-recheck/baseline record binding, current source/pin hashes, the ten zero exits and explicit `-j1 -M4096` commands, their logs/outputs, and all 115 reused source/output identities and successful baseline logs. Independently rebuilding the local import graph gives exactly the recorded ten-module affected closure. Actual Audit-log names and axiom sets match `Audit.lean` and the record, with only the three permitted standard axioms. Current metadata-validation hashes and all seven result/contract names also match.

The problem/manuscript, Definitions, TargetProof, Challenge, Solution, and Comparator retain their previously reviewed hashes. The manuscript remains `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`; the Target definition remains `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`. The phase edit is the separately reviewed same-statement tactic repair. This report does not re-prove all intermediate mathematics.

Historical hashes retain their dated scopes: the earlier complete 125-source record `497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5` predates the phase repair and higher Lake default; the latest record `bcb21102dcd847a244595c04f6cd759b7221b4bd0c0e674beef969ed6eea9c3a` supplies the current 10/115 evidence. Earlier referee reports are not recast as new compiler executions or whole-project re-reviews.

The 4096 MiB serial local workflow and 6144 MiB ordinary-Lake default are distinguished correctly, including the default's effect on ordinary local Lake builds. Both prior Linux attempts remain recorded as failures. These documents assert no current complete-target Comparator/default-kernel/sandbox acceptance. The dated snapshot leaves subsequent Linux publication evidence separate. Memory measurements are not presented as proof of a material reduction or an isolated Linux diagnosis.

The copy receipt binds **exactly 1,422 ordinary published files, totaling 4,041,788 bytes, excluding itself**. I recomputed all listed hashes and compared the full file set: no mismatch, omission, unlisted file, or self-reference. No compiled artifacts or dependency caches were copied. Its proof-record hash equals the actual latest phase-recheck record, and all proof/pin hashes match. This external report does not alter that receipt's project scope.

The proof-project files remain unchanged from the reviewed commit. Repository HEAD advanced during the review, but a path-scoped comparison confirmed no proof-project difference; unrelated changes were not inspected.

| Reviewed file | SHA256 |
| --- | --- |
| `README.md` | `cf3540e2c4898a1ce893350c2cd6d4293fdeea59ae4b2fade26e212441f65906` |
| `VERIFICATION.md` | `d21c712fd94a43c5776a133ce76a1dbfefe7d9e371f20519bd5cae3353ef4eba` |
| `formalization.yaml` | `e5252015127a1ea8a86d4ea79f38694740f5f1d10b3624bc1ca8500d05a1c5da` |
| `evidence/publication/source-copy.json` | `506319b2fc3fc376cfc27b6eb29cae0e80c137125486da2205474ffc71bc040d` |
| `evidence/runs/20260921T014829335357Z-phase-recheck/record.json` | `bcb21102dcd847a244595c04f6cd759b7221b4bd0c0e674beef969ed6eea9c3a` |
| `evidence/runs/20260921T014829335357Z-phase-recheck/Audit.log` | `a1e73e7919dc4a8877bf5e2814c9b225c8781739818459a6170f50d7d646d098` |
| `evidence/metadata-validation.json` | `6b4bf550d448485c46afeba3a6d7d8152826b78be568be627090a622f96cc10e` |

Final observed repository HEAD: `0d314d9957d9a7b68ac4af125ed7e527a4683e52`; reviewed proof-project bytes remain those of `fe2183e9b570322d7c1f64bba3480460082af8d3`.

This is a read-only evidence/metadata approval, not an independent Lean execution or Linux acceptance. It adds no mathematical-resolution or completed-verification count.

Report UTC: 2026-09-21T02:03:35.805538+00:00
