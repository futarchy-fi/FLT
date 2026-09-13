/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Norms of unramified Satake parameters

This is cartography node CBC-S2.  At an unramified place of residue degree `f`, cyclic
base change sends each Satake eigenvalue to its `f`-th power.  The structure here is the
small statement-layer interface; it deliberately does not model Hecke actions or ramified
local base change.
-/

@[expose] public section

namespace CyclicBaseChange

universe u

/-- The two eigenvalues of an unramified rank-two Satake parameter. -/
structure SatakeParam (R : Type u) where
  /-- First Satake eigenvalue. -/
  first : R
  /-- Second Satake eigenvalue. -/
  second : R

namespace SatakeParam

/-- Norm a Satake parameter through an unramified extension of residue degree `f`.

This is the statement-layer norm in `cartography/cbc-reconciled.md`, node S2; the
deferred local base-change proof is ledger item D-2. -/
def norm {R : Type u} [Monoid R] (f : ℕ) (a : SatakeParam R) : SatakeParam R :=
  ⟨a.first ^ f, a.second ^ f⟩

@[simp]
theorem norm_first {R : Type u} [Monoid R] (f : ℕ) (a : SatakeParam R) :
    (a.norm f).first = a.first ^ f :=
  rfl

@[simp]
theorem norm_second {R : Type u} [Monoid R] (f : ℕ) (a : SatakeParam R) :
    (a.norm f).second = a.second ^ f :=
  rfl

end SatakeParam

end CyclicBaseChange
