/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingPairInvariantFlatScalars
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Scalar-compatible coordinates from actual original relation arrows

An original relation arrow with a prescribed first endpoint induces a source
coordinate over the full original invariant ring. The scalar action on the
test is identified with that endpoint, without expanding a canonical algebra
instance through the geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelationOriginalScalarCoordinate
open RingPairInvariantFlatScalars
variable {D A T : Scheme.{0}} (p q : D ⟶ A)
attribute [local instance] sourceAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
variable [Algebra (invariants p.appTop.hom q.appTop.hom) Γ(T, ⊤)]
  (b : T ⟶ A)
  (hscalar : algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(T, ⊤) =
    b.appTop.hom.comp (Subring.subtype (invariants p.appTop.hom q.appTop.hom)))
  (u : T ⟶ D) (hu : u ≫ p = b)

/-- The second endpoint of an original arrow preserves all original invariant scalars. -/
def coordinate : Γ(A, ⊤) →ₐ[R] Γ(T, ⊤) where
  toRingHom := (u ≫ q).appTop.hom
  commutes' r := by
    change u.appTop (q.appTop r.val) = algebraMap R Γ(T, ⊤) r
    rw [← r.property]
    have he : u.appTop (p.appTop r.val) = b.appTop r.val :=
      congrArg (fun f : T ⟶ A ↦ f.appTop r.val) hu
    exact he.trans (DFunLike.congr_fun hscalar r).symm

/-- The constructed algebra map retains the actual original coefficient map. -/
theorem coordinate_toRingHom :
    (coordinate p q b hscalar u hu).toRingHom = (u ≫ q).appTop.hom := rfl

end FLT.Mazur.RelationOriginalScalarCoordinate
