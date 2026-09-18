# Numerical obligations, fixed before proof implementation

No interval grid over matrix entries, dimensions, spectra, k or p is valid or
needed. The target is universal over arbitrary complex PD pairs and real
exponents, including unbounded k. Finite sampling cannot establish it.

C01 proposes precisely

    (0 : Real) < 1/2 and (1/2 : Real) < 1.

Use a single constant dyadic expression and the pinned LeanCert kernel-mode
checked strict-bound certificates. No interval subdivision is required. The
certificate must be consumed in the actual CFC half-power/root identity route
to C02/C03 and hence C20; a final theorem-body dependency diagnostic must confirm
that route. A disconnected decorative LeanCert theorem does not satisfy this
plan. No certificate has been computed for MI28 yet.

All variable-parameter obligations must use exact symbolic real arithmetic,
with strict denominator hypotheses made explicit:

* k,p>0 imply k+1, k+2, k+p>0; no division by zero in r=2/k or a=2/p.
* k/(k+1)≤p≤1 implies Furuta's (1+2/k)2≥2/p+2/k.
* k>0 and 1≤p≤2 imply 1≤p≤s≤2 for s=p(k+2)/(k+p), q=2/s≥1,
  (1+2/k)q=2/p+2/k, 0<2/(k+2)≤1,
  0≤p−1≤1 and 0≤(k−p+2)/(k+2)≤1.
* In the swap, 0<p≤k gives 0<p/k≤1 and 0≤(k−p)/k≤1, including zero.
* The Furuta extension at N≥0 uses a1=(a+N)/(1+N)≥1 and
  t=(r−N)/(1+N) in [0,1]; no rounding or approximate ceiling enters the proof.
* Homogeneity uses c>0, p>0 and (c^(-1/p))^p=c^(-1).
* Endpoint k_m=1/(m+1) is positive, at most two, and tends to zero.
* Scalar determinant weights a/(1+a) are positive for a>0, bounded above by
  one, and increasing in a. Logs are applied only to strictly positive numbers.

The branches p=0 and k=0 are handled before any reciprocal exponent is used.
This preserves the original closed parameter ranges. Machine-floating-point
or finite integer examples are not part of the logical argument.
