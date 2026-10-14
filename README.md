# PrincipalBundles

Principal bundles, connections and the exponential map of a Lie group in Lean 4, as a
stand-alone Lake project on top of Mathlib. Moved out of the `smooth-exp-Lie-V` branch of
`idontgetoutmuch/mathlib4` (tip `1132f60`).

## Layout

- `PrincipalBundles/` — the development:
  - `ExpLie.lean` — `expLie` and its smoothness (`contMDiff_expLie`).
  - `FakeFormIII.lean` — `IsPrincipalBundle`, connection forms, `yangMills_transformation`.
  - `FrameBundle.lean`, `UnitsMFDeriv.lean`, `FundamentalVF.lean`, `GradedDiffLieAlg.lean`,
    `SmoothRightGAction.lean`.
- `TauCeti/` — files copied unchanged from Tau Ceti for the maximal flow of a vector field
  (Lee Thm 9.12); see `TauCeti/VENDORED.md`.
- `attic/` — not built. `MaximalFlow.lean` (the continuous Lee 9.12, superseded by Tau Ceti's
  flow; it needs Winston Yin's unmerged mathlib4#26394) and `IntegralCurveCompact.lean`.
- `docs/GEOMETRY_HANDOFF.md` — notes carried over from the branch.

## Build

```
lake exe cache get
lake build
```

Mathlib is pinned to `3b531c35df33d6bbe64b4e87dec056211d3a5676`, the commit Tau Ceti builds
against, so the vendored files compile unchanged.

## Axioms

None. `contMDiff_flow_like` is now a theorem, proved from Tau Ceti's `globalFlow`; the price
is `[FiniteDimensional ℝ EG]` on `contMDiff_expLie` and in `FakeFormIII.lean`.
