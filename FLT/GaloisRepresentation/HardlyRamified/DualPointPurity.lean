/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PureAction
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Transferring pointwise purity through a dual pairing

An equivariant pairing that separates points transfers a scalar action on its
values to the first factor when the second factor has trivial action. A Cartier
pairing would supply these hypotheses for the multiplicative-filtration argument;
constructing that pairing for finite-flat models is a separate theorem.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- An equivariant bilinear pairing separating the first variable transfers purity
from its values when the second variable has trivial group action. -/
theorem pure_of_separating_pairing
    {G R W V T : Type*} [CommRing R]
    [AddCommGroup W] [AddCommGroup V] [AddCommGroup T]
    [Module R W] [Module R V] [Module R T]
    [SMul G W] [SMul G V] [SMul G T]
    (e : W →ₗ[R] V →ₗ[R] T) (he : Function.Injective e)
    (hequiv : ∀ (g : G) (w : W) (v : V), e (g • w) (g • v) = g • e w v)
    (hV : ∀ (g : G) (v : V), g • v = v)
    (χ : G → R) (hT : Pure T χ) : Pure W χ := by
  intro g w
  apply he
  apply LinearMap.ext
  intro v
  calc
    e (g • w) v = e (g • w) (g • v) := by rw [hV]
    _ = g • e w v := hequiv g w v
    _ = χ g • e w v := hT g (e w v)
    _ = e (χ g • w) v := by simp

end ThreeAdicPlan
