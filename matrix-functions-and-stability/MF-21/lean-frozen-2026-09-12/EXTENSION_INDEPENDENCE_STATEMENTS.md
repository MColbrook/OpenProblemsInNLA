# Independence of the smooth extensions and implicit choice

Locked before ExtensionIndependence.lean and SmoothCoefficient.lean,
20 September 2026.

Fix the actual manuscriptEta, symbol, and a constructed phase Y carrying
the uniform uniqueness statement already proved in ImplicitPhase. Its
coefficient family is precisely implicitPhaseCoefficient m Y k.

Let etaTilde and gTilde agree respectively with manuscriptEta and symbol
on [0,pi]. Let Z be another smooth implicit parametrization near the
zero-height segment, with Z(x,0)=x, and with

    Z(x,h)=x+h*etaTilde(Z(x,h))

as a germ in h at zero for each interior x. Require ContDiffAt Real
infty (smooth order, not analytic top) of Z at every (x,0), and of
gTilde at every x, for x in [0,pi]. The actual Y is smooth there as a
consequence of its already proved stronger analytic regularity. These
are the natural properties of the competing smooth-extension/implicit
construction. No equality of coefficients or solutions is a premise.

Conclusion: for every natural k, the exact derivative/factorial
coefficient of gTilde(Z(x,h)) at h=0 equals
implicitPhaseCoefficient m Y k x for every x in [0,pi].

At interior x, continuity keeps Z inside (0,pi) for small h. Agreement
of etaTilde with eta and the actual uniform uniqueness identify Z with
Y as germs in h. Agreement of gTilde with g then identifies the composed
germs and hence every iterated derivative. Endpoint coefficients are
obtained by continuity in x and closure((0,pi))=[0,pi], rather than an
unjustified claim that all endpoint solution values stay in the interval.

SmoothCoefficient will first prove that the exact vertical iterated
derivatives and their factorial coefficients remain smooth when the
joint function is C-infinity. This uses the pinned Mathlib parametric
Frechet derivative API; in this pin the order infty is distinct from
top=omega (analytic). No analytic regularity of the arbitrary extensions
will be assumed.

The theorem also implies independence of radii and totalization choices
for the same extension. It does not assert that Y itself is unchanged
away from h=0 or that different extensions agree outside [0,pi]. This
is an auxiliary manuscript claim, separate from the spectral target.
