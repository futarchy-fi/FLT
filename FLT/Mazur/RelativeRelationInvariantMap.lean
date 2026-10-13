/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocallyRinged

/-!
# Maps of original invariant locally ringed quotients

A map of full relations induces a map including the invariant structure
sheaves. Different coefficient bases are allowed. No scheme representation
or effectiveness of either quotient is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')

/-- The explicit invariant projection identifies both entire relation maps. -/
@[reassoc]
theorem invariantProjection_condition :
    p.left.toLRSHom ≫ invariantLocallyRingedProjection e =
      q.left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  unfold invariantLocallyRingedProjection locallyRingedProjection
  exact coequalizer.condition_assoc _ _ _

/-- Maps from the invariant quotient are determined by the original source. -/
theorem invariantMap_hom_ext {Z : LocallyRingedSpace.{u}}
    {v w : invariantLocallyRingedSpace e ⟶ Z}
    (h : invariantLocallyRingedProjection e ≫ v =
      invariantLocallyRingedProjection e ≫ w) : v = w := by
  let _ : Epi (invariantLocallyRingedProjection e) := by
    unfold invariantLocallyRingedProjection locallyRingedProjection
    infer_instance
  exact (cancel_epi (invariantLocallyRingedProjection e)).mp h

variable (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)

include hp hq in
/-- A map of the full relation makes the source comparison invariant. -/
theorem invariantMap_condition :
    p'.left.toLRSHom ≫ g.toLRSHom ≫ invariantLocallyRingedProjection e =
      q'.left.toLRSHom ≫ g.toLRSHom ≫ invariantLocallyRingedProjection e := by
  rw [← Scheme.Hom.comp_toLRSHom_assoc, ← hp, Scheme.Hom.comp_toLRSHom_assoc,
    invariantProjection_condition, ← Scheme.Hom.comp_toLRSHom_assoc, hq,
    Scheme.Hom.comp_toLRSHom_assoc]

/-- The map of full relations descends to the actual invariant locally ringed spaces. -/
def invariantMap : invariantLocallyRingedSpace e' ⟶ invariantLocallyRingedSpace e :=
  (invariantLocallyRingedIso e').inv ≫ coequalizer.desc
    (g.toLRSHom ≫ invariantLocallyRingedProjection e)
    (invariantMap_condition e g r hp hq)

/-- The descended morphism retains the original source comparison. -/
@[reassoc]
theorem invariantMap_projection :
    invariantLocallyRingedProjection e' ≫ invariantMap e e' g r hp hq =
      g.toLRSHom ≫ invariantLocallyRingedProjection e := by
  dsimp only [invariantMap, invariantLocallyRingedProjection]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

/-- On every source point the quotient map is the original geometric map. -/
theorem invariantMap_projection_apply (x : U'.left) :
    (invariantMap e e' g r hp hq).base (projection e' x) = projection e (g x) := by
  have h := congrArg (fun k ↦ k.base) (invariantMap_projection e e' g r hp hq)
  rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
    invariantLocallyRingedProjection_base, invariantLocallyRingedProjection_base] at h
  exact congrArg (fun k ↦ k x) h

/-- The descended morphism respects the original change of coefficient base. -/
theorem invariantMap_base (b : S' ⟶ S) (hb : g ≫ U.hom = U'.hom ≫ b) :
    invariantMap e e' g r hp hq ≫ invariantLocallyRingedBaseMap e =
      invariantLocallyRingedBaseMap e' ≫ b.toLRSHom := by
  apply invariantMap_hom_ext e'
  rw [invariantMap_projection_assoc, invariantLocallyRingedProjection_baseMap,
    ← Category.assoc, invariantLocallyRingedProjection_baseMap,
    ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, hb]

end FLT.Mazur.RelativeRelationOrbit
