/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelationOriginalScalarCoordinate

/-!
# Original scalar coordinates with prescribed endpoint maps

Retain the literal second endpoint ring map when constructing its scalar
compatibility from an original relation arrow. This keeps specialization to
nested geometric maps independent of their expanded definitions.
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
  (b v : T ⟶ A)
  (hscalar : algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(T, ⊤) =
    b.appTop.hom.comp (Subring.subtype (invariants p.appTop.hom q.appTop.hom)))
  (u : T ⟶ D) (hu : u ≫ p = b) (hv : u ≫ q = v)

/-- The actual second endpoint becomes an algebra map over the original invariant ring. -/
def endpointCoordinate : Γ(A, ⊤) →ₐ[R] Γ(T, ⊤) where
  toRingHom := v.appTop.hom
  commutes' r := by
    have he := congrArg (fun g : T ⟶ A ↦ g.appTop r.val) hv
    exact he.symm.trans ((coordinate p q b hscalar u hu).commutes r)

/-- The underlying map is definitionally the prescribed second endpoint. -/
theorem endpointCoordinate_toRingHom :
    (endpointCoordinate p q b v hscalar u hu hv).toRingHom = v.appTop.hom := rfl

end FLT.Mazur.RelationOriginalScalarCoordinate
