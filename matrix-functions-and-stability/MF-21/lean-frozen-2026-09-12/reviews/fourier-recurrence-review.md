# Independent Fourier endpoint and recurrence review

Verdict: **APPROVE** the seven public declarations in FourierEndpoint, FourierRecurrence, and FourierRecurrenceEquation at the hashes below. Their types match the three statement locks and faithfully bridge the actual Fourier coefficients to the normalized recurrence used after manuscript (13).

The coordinator reports Endpoint01, Recurrence01, and Equation01 each exited 0 on these sources. I read the logs: the four endpoint theorems, two shifted-polynomial/characteristic-root theorems, and one equation equivalence all report only `[propext, Classical.choice, Quot.sound]`. I ran no compiler, Lake, Comparator, or GitHub workflow. This is independent mathematical/source review, not an independent execution claim. No reviewed source was edited.

## Endpoint and normalization

`FourierEndpoint.fourierCoeff_right_endpoint` (lines 16–31) applies the already proved concrete coefficient recurrence at the next outer frequency. Both larger-frequency terms vanish by the established support theorem, leaving minus the old endpoint. Thus the result is exactly (-1)^m. The negative endpoint follows from evenness of the actual cosine coefficient (lines 35–37). Both nonzero statements are then derived, not assumed. Order zero is included correctly: both endpoints coincide at frequency zero with coefficient 1.

The imports ultimately use `Definitions.fourierCoeff`, the normalized integral of the published even symbol. The previous independent stencil/Laurent review established the integral and Fourier-convention connection; this module does not replace that coefficient with an arbitrary recurrence array. With the support theorem, these endpoint results establish exact half-bandwidth m and justify every later division by the endpoint.

## Shifted polynomial and characteristic root

`FourierRecurrence.fourierCoeff_shifted_laurent_sum` (lines 23–56) reindexes exactly k=t-m from Fin(2m+1) to the inclusive integer interval [-m,m]. Its inverse uses (k+m).toNat only after proving k+m≥0, and the index bound is explicit. Multiplication by z^m and integer-power addition give natural exponents t. This is the same Laurent polynomial `(2-z-z⁻¹)^m` used in the manuscript. Nonzero z is necessary: at m=1,z=0 the polynomial-side constant term is -1 while the totalized right side would be 0. The theorem correctly excludes that case.

`fourierRecurrence` (lines 60–65) has order 2m and coefficients `(δ_(i,m) λ - a_(i-m))/a_m`. Therefore its actual Mathlib convention is

`u(k+2m) = Σ_(i<2m) ((δ_(i,m)λ-a_(i-m))/a_m) u(k+i)`.

The denominator is a_m=(-1)^m, and the spectral term is at index m. Neither its sign nor its center is shifted. For the concrete check m=1 this becomes `u(k+2)=(2-λ)u(k+1)-u(k)`, equivalent to the usual three-point stencil. For m=2 it rearranges to the five-point coefficients 1,-4,6,-4,1, with λ at the central value.

`fourierRecurrence_charPoly_isRoot` (lines 69–133) splits the full shifted sum at the actual terminal t=2m, evaluates the central singleton t=m, uses the proved nonzero endpoint, and obtains the exact Mathlib characteristic-polynomial equation. It proves the stated implication from the nonzero Laurent spectral root to a characteristic root. It does not assert all roots have already been constructed, are distinct, or have a prescribed modulus.

The m≥1 hypothesis is necessary for these spectral recurrence results, because the central and terminal positions must differ. At m=0 the total definition remains well typed, but a λ=1 spectral equation would impose no condition, whereas an order-zero Mathlib recurrence forces the zero sequence. The theorem does not incorrectly include that case.

## Pointwise equation equivalence

`FourierRecurrenceEquation.fourierRecurrence_equation_iff` (lines 17–92) uses the same recurrence definition and arbitrary complex λ, sequence u, and natural k. It splits off exactly the terminal t=2m value and evaluates exactly the central t=m value, then reversibly multiplies by the proved nonzero endpoint. Both directions are proved. No solution premise, geometric representation, finite-support assumption on u, ghost value, or spectral limit is smuggled into the statement.

The right side includes all frequencies -m,...,m, and the central sample is u(k+m). To connect it to a finite Toeplitz row, the separate zero-extension/reindexing theorem must also use evenness to reconcile a_(j-i) with the Toeplitz convention a_(i-j). That finite-matrix bridge is not claimed by these three modules. Neither are a boundary-kernel/eigenvalue equivalence, multiplicity equality, root indexing, or any asymptotic part of MF-21.

No material issue was found. The proof reuses existing finite-sum, integer-power, endpoint and linear-recurrence APIs, with symbolic algebra only; no numerical certification or brute-force check is needed. These are concrete source-faithful ingredients and do not increase the completed original-problem count.

## Frozen source and evidence

| File | SHA256 |
|---|---|
| `MF21Restart/FourierEndpoint.lean` | `fe02eb29990ee0b5c642a23000e88cb6e2e7ee956d700a884b36fed9bba6dabe` |
| `MF21Restart/FourierRecurrence.lean` | `99c431d06aea02d723c4e95e4b8aabcff51af0fc5b0cc0bca0b95d1bddaab9c8` |
| `MF21Restart/FourierRecurrenceEquation.lean` | `49d55d4312ac773733627b284f6319dd7c45319b24a6cbebf5914b280e78eb7d` |
| `FOURIER_ENDPOINT_STATEMENTS.md` | `92b0707cc6301215462509a3e294b7b6493ef7dcc73355442e61aefb687c1e75` |
| `FOURIER_RECURRENCE_STATEMENTS.md` | `018a827a3b1ac5b73edcd51d86993c0c06f1f4b658a6a52cf8c1412f0d448960` |
| `FOURIER_RECURRENCE_EQUATION_STATEMENTS.md` | `ee9b1659d03f8dbda6efe2bed9cdb79f003a71df1164ad2551c8e6dd97bf47c3` |
| `MF21Restart/FourierStencil.lean` | `c7c94724b95fffb35abf8f682a921a0badcca1de19e41b99b0502cd9349cf809` |
| `MF21Restart/FourierLaurent.lean` | `ffa0cb9a4f88ba83f76d5101875fc9e8065bbc3c7e582e0808be6bc939c69dad` |
| `MF21Restart/Definitions.lean` | `35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51` |
| `evidence/logs/fourier-endpoint-01.log` | `8ab4276dbc9ff1dc368a4dfb6d8bfa792d1902dcbe56982f138ca5ed59af5774` |
| `evidence/logs/fourier-recurrence-01.log` | `9b993a5404941af434dfa2c020ead237a1f35ffef8e7895c431a09ae65ad671f` |
| `evidence/logs/fourier-equation-01.log` | `0e4fd7e645baa776c2cd614fa04953ed2fa510cedd8ed3e7ac8379d90940d447` |
