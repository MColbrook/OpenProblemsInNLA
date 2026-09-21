# Right-grid averages of a continuous function

Locked before GridAverage.lean, 20 September 2026.

For an actual real function f continuous on [0,1], prove

```
lim_{n->infinity} (1/n) * sum_{i:Fin n} f((i+1)/n) = integral_0^1 f.
```

Use the already proved cell integral estimate and compact uniform
continuity, with no asserted quadrature estimate as a premise. This
includes the upper endpoint 1 and uses exactly the grid of the actual
inverse entries. The totalized n=0 value is immaterial to the limit.
