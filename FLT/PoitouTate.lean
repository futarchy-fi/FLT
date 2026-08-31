/-
Copyright (c) 2026 kas.eth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kas.eth
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Poitou–Tate statement-layer scaffold

This module packages the finite discrete consequences of the Poitou–Tate
sequence and the Greenberg–Wiles order formula as a compiling statement layer.

The displayed theorem is the Greenberg–Wiles order formula, following
NSW, Theorem 8.7.9, and Darmon–Diamond–Taylor, Theorem 2.18, as the
displayed source, with Wiles, Proposition 1.6, as the originating special case
and Milne, Arithmetic Duality Theorems, I.4.20, as the finitely generated
generalization cited by Wiles.

## Permanent deferred-obligation ledger

The full topologized nine-term sequence and Sha-duality are deferred, never
deleted. The panel-deleted middle-exactness node is explicitly excluded from
this package.
-/

@[expose] public section

open Finset

universe u v w

/-- Cartier/Tate dual of a finite discrete module, as a genuine additive
hom-type into a supplied roots-of-unity coefficient type. -/
abbrev CartierDual (M mu : Type u) [AddCommGroup M] [AddCommGroup mu] := M →+ mu

/-- Carrier data exposing the objects occurring in the Greenberg–Wiles order
formula. The carrier families are parameterized by the finite discrete
coefficient-module type. Local families additionally take a place. -/
structure PoitouTateData (Place : Type v) (mu : Type u) [AddCommGroup mu] where
  /-- Global degree-zero cohomology of a coefficient module. -/
  H0 : Type u → Type w
  /-- Global degree-one cohomology of a coefficient module. -/
  H1 : Type u → Type w
  /-- Unramified degree-one cohomology of a coefficient module. -/
  H1nr : Type u → Type w
  /-- Degree-one Selmer group determined by the chosen local conditions. -/
  selmerH1 : Type u → Type w
  /-- Degree-one Selmer group for the orthogonal local conditions. -/
  selmerH1Perp : Type u → Type w
  /-- Local degree-zero cohomology at a place. -/
  localH0 : Place → Type u → Type w
  /-- Local degree-one cohomology at a place. -/
  localH1 : Place → Type u → Type w
  /-- Chosen local condition at a place. -/
  localCondition : Place → Type u → Type w
  /-- Orthogonal local condition at a place. -/
  localConditionPerp : Place → Type u → Type w
  /-- Localization from global to local degree-one cohomology. -/
  localizationMap : {M : Type u} → H1 M → (place : Place) → localH1 place M
  /-- Local duality pairing between a module and its Cartier dual. -/
  localPairing : {M : Type u} → [AddCommGroup M] → (place : Place) →
    localH1 place M → localH1 place (CartierDual M mu) → mu

/-- The Greenberg–Wiles order formula, stated as a cross-multiplied equality
of natural cardinalities. The displayed mathematical content is
`#H¹_L / #H¹_{L_perp} = (#H⁰(K,M) / #H⁰(K,M*)) · ∏_v (#L_v / #H⁰(K_v,M))`.
-/
theorem greenbergWilesOrderFormula {Place : Type v} {mu M : Type u}
    [AddCommGroup mu] [AddCommGroup M] (data : PoitouTateData Place mu)
    [Finite Place] [Fintype Place] [Finite (data.H0 M)]
    [Finite (data.H0 (CartierDual M mu))] [Finite (data.selmerH1 M)]
    [Finite (data.selmerH1Perp (CartierDual M mu))]
    [∀ place : Place, Finite (data.localCondition place M)]
    [∀ place : Place, Finite (data.localH0 place M)] :
    Nat.card (data.selmerH1 M) * Nat.card (data.H0 (CartierDual M mu)) *
        ∏ place : Place, Nat.card (data.localH0 place M) =
      Nat.card (data.selmerH1Perp (CartierDual M mu)) * Nat.card (data.H0 M) *
        ∏ place : Place, Nat.card (data.localCondition place M) := by
  sorry
