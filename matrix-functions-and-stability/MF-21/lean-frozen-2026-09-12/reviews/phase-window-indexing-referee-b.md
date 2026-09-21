# Independent review: actual phase-window indexing

Verdict: **APPROVE** for `eigenvalue_eventual_phase_window`.
Reviewer: `/root/mf21_restart_manuscript`, independently of source author
`/root/mf21_restart_lean_audit`. Completed 20 September 2026 under the
pinned referee rubric (SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`).

I read the complete new source, its prior statement lock, the relevant
unchanged manuscript Lemma 4, and the exact local test record/log. This
review concerns the new indexing argument and the discharge of its
imported theorem hypotheses. It does **not** independently re-review my
own upstream `SpectralOrder`, `PhaseWindowRoots`, `PhaseRootCoverage`,
or `ActualSimpleRoots` proofs. Those dependencies need the separately
assigned independent review. The abstract `OrderedTailCounting` proof
has my separate independent report.

## Exact artifacts and actual evidence

| Artifact | SHA256 |
| --- | --- |
| `MF21Restart/PhaseWindowIndexing.lean` | `8b99a37e436dfe7f4e8efbf39de6d091f511d62e5634e6c405dc2a00ffff1117` |
| `PHASE_WINDOW_INDEXING_STATEMENTS.md` | `f32b24632bdfd630d1bc7d047521bc505f2f7e6e0b9788cd8b0699d94a7ae586` |
| `evidence/logs/phase-window-indexing-01.json` | `983315d8ddef98d9a4fac47a114cbb269228eb4d08decc77bb2078b235aea005` |
| `evidence/logs/phase-window-indexing-01.log` | `d3756ed040cd70c376fc8c95f23da57c22fa707eed6a64959d1b36530b5d91fa` |
| `.lake/build/lib/lean/MF21Restart/PhaseWindowIndexing.olean` | `c4bca5b1a3051a3e8c87b5f316b608a215ed3b1692825f832ba254272d62cb91` |

The displayed hashes were recomputed. Source/log/output match the
retained JSON, which records exit code 0, unchanged source, and
`LEAN_NUM_THREADS=1` for the actual command
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/PhaseWindowIndexing.olean MF21Restart/PhaseWindowIndexing.lean`.
The log prints only `propext`, `Classical.choice`, and `Quot.sound` for
the theorem. I ran no Lean compiler. No Comparator run is represented
by this local evidence or by this report.

## Mathematical and statement audit

The final statement matches its lock and uses the original one-based
accessor `eigenvalue m n j`, the original symbol, and the actual phase
and residual. The positive thresholds depend on m alone. The proof
chooses N also at least J, so the asserted tail exists for all n>=N.
It concludes an interior angle with the actual eigenvalue, the j-th
phase cell, residual zero, and nonzero residual derivative. This is
precisely the indexing/simplicity portion of manuscript Lemma 4.

The local root family is chosen only on J,...,n. Its zero default is
never used as a spectral angle. Quarter-period cells with distinct
natural labels are strictly ordered: adjacent cells leave a half-period
gap. Actual strict phase monotonicity therefore orders their angles,
and actual strict symbol monotonicity orders their values. Every
selected root has nonzero residual derivative from the actual root
window theorem, and the concrete simple-root theorem gives its unique
original one-based eigenvalue occurrence. The private conversion to a
`Fin n` position proves both existence and uniqueness and correctly
handles j-1 and i.val+1.

The critical coverage premise is discharged for every sorted array
position with value at least the first selected tail value. The actual
spectral angle exists by strict enclosure and symbol inversion. Symbol
and phase order put that angle above the first selected root, and the
eigenvalue criterion makes it a residual zero. The combined threshold
J is at least the coverage threshold. The coverage theorem can initially
return a label below J; the proof explicitly rules this out using the
strict separation of its cell from the J-cell and the opposite phase
ordering. It then uses uniqueness of the actual cell root to identify
the angle. There is no unstated assumption excluding intervening or
larger eigenvalues, and multiplicities are counted as array positions.

All four premises of `ordered_tail_index` are thus supplied by actual
project results. Its conclusion identifies zero-based position j-1;
the final explicit `eigenvalue_in_range` rewrite gives the unchanged
one-based accessor. No renumbering, omission of repeated low values,
or alternate spectral list is introduced. No material issue found.

The source contains no custom axiom, proof placeholder, numerical
certificate, or assumed desired index equality. The finite counting
and monotonicity APIs are reused at a suitable level of generality.

## Remaining scope

This does not prove the exponential phase displacement or the bounds
in (19), does not construct Y, and does not prove any Taylor expansion,
uniform kernel limit, or full MF-21 target. It completes the concrete
original-index identification after its independently checked analytic
and spectral prerequisites are supplied; a green local test alone is
not a full Comparator or target claim.
