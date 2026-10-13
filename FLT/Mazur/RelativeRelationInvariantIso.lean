/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantMap

/-!
# Isomorphisms of original invariant locally ringed quotients

An isomorphism of the full scheme relation diagrams induces an isomorphism
of the explicit invariant locally ringed spaces, including their sheaves.
The construction allows different coefficient bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ≅ U.left) (r : A'.left ≅ A.left)
  (hp : r.hom ≫ p.left = p'.left ≫ g.hom)
  (hq : r.hom ≫ q.left = q'.left ≫ g.hom)

include hp in
/-- The inverse diagram retains the first original endpoint. -/
theorem invariantIso_inverse_fst : r.inv ≫ p'.left = p.left ≫ g.inv := by
  apply (cancel_epi r.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, hp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

include hq in
/-- The inverse diagram also retains the second endpoint. -/
theorem invariantIso_inverse_snd : r.inv ≫ q'.left = q.left ≫ g.inv := by
  apply (cancel_epi r.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, hq, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The inverse comparison of the actual invariant locally ringed spaces. -/
def invariantIsoInverse : invariantLocallyRingedSpace e ⟶ invariantLocallyRingedSpace e' :=
  invariantMap e' e g.inv r.inv (invariantIso_inverse_fst g r hp)
    (invariantIso_inverse_snd g r hq)

/-- The inverse comparison recovers the inverse original source morphism. -/
@[reassoc]
theorem invariantIsoInverse_projection :
    invariantLocallyRingedProjection e ≫ invariantIsoInverse e e' g r hp hq =
      g.inv.toLRSHom ≫ invariantLocallyRingedProjection e' :=
  invariantMap_projection _ _ _ _ _ _

/-- Full relation diagram isomorphisms give actual invariant locally ringed isomorphisms. -/
def invariantIso : invariantLocallyRingedSpace e' ≅ invariantLocallyRingedSpace e where
  hom := invariantMap e e' g.hom r.hom hp hq
  inv := invariantIsoInverse e e' g r hp hq
  hom_inv_id := by
    apply invariantMap_hom_ext e'
    rw [invariantMap_projection_assoc, invariantIsoInverse_projection,
      ← Scheme.Hom.comp_toLRSHom_assoc, g.hom_inv_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  inv_hom_id := by
    apply invariantMap_hom_ext e
    rw [invariantIsoInverse_projection_assoc, invariantMap_projection,
      ← Scheme.Hom.comp_toLRSHom_assoc, g.inv_hom_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The isomorphism's forward map is the original relation comparison. -/
theorem invariantIso_hom : (invariantIso e e' g r hp hq).hom =
    invariantMap e e' g.hom r.hom hp hq := rfl

end FLT.Mazur.RelativeRelationOrbit
