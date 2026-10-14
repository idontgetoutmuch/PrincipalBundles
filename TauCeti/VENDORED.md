# Vendored Tau Ceti files

These files are copied unchanged from https://github.com/TauCetiProject/TauCeti
at commit 43e35ca36bede59dc22464fcef2c9323ff3c86fe (2026-10-14), under the Apache 2.0
licence in `LICENSE` in this directory. Copyright: the Tau Ceti contributors.

They are the import closure of `TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow`
(the maximal flow of a vector field and its joint smoothness, Lee Thm 9.12, for
finite-dimensional models). Tau Ceti builds them against Mathlib
3b531c35df33d6bbe64b4e87dec056211d3a5676, which is the pin in this project's lakefile.

Do not edit them here; to update, re-copy the closure from a newer Tau Ceti commit
and move the Mathlib pin and `lean-toolchain` to match its `lake-manifest.json`.
