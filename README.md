# PrincipalBundles

Principal bundles, connections and the exponential map of a Lie group in Lean 4, as a
stand-alone Lake project on top of Mathlib. Moved out of the `smooth-exp-Lie-V` branch of
`idontgetoutmuch/mathlib4` (tip `1132f60`) and the `diff-forms-application` branch of
`idontgetoutmuch/DeRhamCohomology` (`fc39c2d`), which split `FakeFormIII.lean` into
`PrincipalBundle`, `FundamentalVectorField`, `ConnectionForm`, `Forms` and `YangMills`.

## Layout

- `PrincipalBundles/` — the development:
  - `ExpLie.lean` — `expLie` and its smoothness (`contMDiff_expLie`).
  - `SmoothRightGAction.lean` — smooth right actions (formerly `PrincipalGBundlePrelude`).
  - `PrincipalBundle.lean` — `IsPrincipalBundle`, local sections, `contMDiffAt_gaugeMap`.
  - `FundamentalVectorField.lean` — fundamental vector fields, `Ad`, `maurerCartan`.
  - `ConnectionForm.lean`, `Forms.lean`, `YangMills.lean` — connection forms,
    `yangMills_transformation`.
  - `UnitsMFDeriv.lean`, `GradedDiffLieAlg.lean`.
  - `FrameBundle.lean` — the frame bundle as a principal `GL(E)`-bundle. Its local
    trivialisations are those of the Hom bundle restricted to invertible frames
    (`Trivialization.restrictUnits`). `frameBundleYangMills_transformation` is the
    gauge transformation law in coordinates.
- `TauCeti/` — files copied unchanged from Tau Ceti for the maximal flow of a vector field
  (Lee Thm 9.12); see `TauCeti/VENDORED.md`.
- `attic/` — not built. `MaximalFlow.lean` (the continuous Lee 9.12, superseded by Tau Ceti's
  flow; it needs Winston Yin's unmerged mathlib4#26394), `IntegralCurveCompact.lean`, and
  `FundamentalVF.lean` (`funVF`, `mlieBracket_funVF`), which still needs porting to this Mathlib.
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
is `[FiniteDimensional ℝ EG]` on `contMDiff_expLie`, in the main `variable` blocks of
`FundamentalVectorField`, `ConnectionForm` and `YangMills`, and `[FiniteDimensional ℝ E]` in
the frame-bundle Yang–Mills section of `FrameBundle.lean`.
