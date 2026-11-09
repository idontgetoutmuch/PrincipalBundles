# Vendored Tau Ceti files

These files are copied unchanged from https://github.com/TauCetiProject/TauCeti
at commit 7134b2f77401e390a72cd2568efe106f3ebda06f (2026-11-09), under the Apache 2.0
licence in `LICENSE` in this directory. Copyright: the Tau Ceti contributors.

They are the import closure of

* `TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow` (the maximal flow of a vector field
  and its joint smoothness, Lee Thm 9.12, for finite-dimensional models), and
* `TauCeti.Geometry.Manifold.FiberBundle.Principal` (Tau Ceti's principal bundles and their
  smooth structure, used by `PrincipalBundles.FrameBundleExample`).

Tau Ceti builds them against Mathlib 1b1ccf4b088b32fa3f23f2de1127433254a81e1e, which is the
pin in this project's lakefile.

Do not edit them here; to update, re-copy the closure from a newer Tau Ceti commit
and move the Mathlib pin, `lake-manifest.json` and `lean-toolchain` to match its
`lake-manifest.json`.
