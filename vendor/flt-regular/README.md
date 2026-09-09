# `flt-regular` compatibility port

This directory vendors the `FltRegular` library used to discharge the small
prime exponents in the FLT proof spine.

The files are based on `projects/FltRegular` at AINTLIB commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.  The last commit in that source
tree which changes `projects/FltRegular` is
`fa3c5e6ee266ce3060bf9964fa3a592c9f8fcd8e`.  AINTLIB records the original
source as `leanprover-community/flt-regular` at revision `6ade127`, followed by
compatibility changes needed for newer Mathlib revisions.

Relative to the attributed AINTLIB tree, this snapshot only renames APIs marked
deprecated by the FLT Mathlib pin (`Prime.not_isUnit`, `ite_true`,
`ite_eq_right`, `dite_eq_left`, and `Finsupp.mapDomain_of_notMem_range`). The
library-specific Lake configuration also suppresses the legacy
`linter.style.haveILetI` style warning. No declaration or proof is otherwise
changed.

We vendor the compatibility port instead of depending on the current upstream
revision because upstream targets Lean `v4.34.0-rc2`, while this repository is
still pinned to `v4.34.0-rc1`.  Keeping this small source snapshot in-tree makes
the exact code compiled by CI reproducible.

The original source headers identify Kevin Kappelmann, Ruben Van de Velde,
Pietro Monticone, and FLT contributors as authors and license the files under
Apache-2.0.  The same license governs this repository; see the root `LICENSE`.
