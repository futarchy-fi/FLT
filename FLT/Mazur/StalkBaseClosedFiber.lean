/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointFiberAmple
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Closed fibers after base change to a stalk

The closed fiber of the family over the base's local ring is the original
scheme-theoretic fiber. The comparison preserves its map to the total space
and therefore transports the actual line sheaf and its ampleness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.StalkBase

open BaseAdicThickening FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/-- The family over the actual local ring at the chosen base point. -/
abbrev family := pullback f (S.fromSpecStalk s)

/-- The structural map of the family over the local ring. -/
abbrev projection : family f s ⟶ Spec (S.presheaf.stalk s) :=
  pullback.snd f (S.fromSpecStalk s)

/-- The map from the family over the local ring to the original total space. -/
abbrev toSource : family f s ⟶ X := pullback.fst f (S.fromSpecStalk s)

/-- The closed fiber over the local ring agrees with the original point fiber. -/
def closedFiberIso :
    (projection f s).fiber (IsLocalRing.closedPoint (S.presheaf.stalk s)) ≅ f.fiber s := by
  let R := S.presheaf.stalk s
  let p := IsLocalRing.closedPoint R
  let _ : p.asIdeal.IsMaximal := inferInstanceAs (IsLocalRing.maximalIdeal R).IsMaximal
  refine asIso (pullback.map (projection f s) ((Spec R).fromSpecResidueField p)
    (projection f s) (Spec.map (S.residue s)) (𝟙 _) (closedPointQuotientIso R p).hom
    (𝟙 _) (by simp) ?_) ≪≫ pullbackLeftPullbackSndIso f (S.fromSpecStalk s)
      (Spec.map (S.residue s))
  simpa only [Category.comp_id, Scheme.residue, IsLocalRing.residue,
    p, IsLocalRing.closedPoint] using (closedPointQuotientIso_hom_map R p).symm

/-- The local closed-fiber comparison is over the original total space. -/
@[reassoc (attr := simp)]
lemma closedFiberIso_hom_ι :
    (closedFiberIso f s).hom ≫ f.fiberι s =
      (projection f s).fiberι (IsLocalRing.closedPoint (S.presheaf.stalk s)) ≫ toSource f s := by
  simp [closedFiberIso, Scheme.Hom.fiberι, Scheme.fromSpecResidueField, toSource]

/-- The line on the local closed fiber is the transported original fiber line. -/
def closedFiberLineIso (L : X.Modules) :
    (Scheme.Modules.pullback ((projection f s).fiberι
      (IsLocalRing.closedPoint (S.presheaf.stalk s)))).obj
        ((Scheme.Modules.pullback (toSource f s)).obj L) ≅
        (Scheme.Modules.pullback (closedFiberIso f s).hom).obj
          ((Scheme.Modules.pullback (f.fiberι s)).obj L) :=
  (pullbackComp _ _).app L ≪≫
    ((pullbackCongr (closedFiberIso_hom_ι f s)).app L).symm ≪≫
      ((pullbackComp _ _).app L).symm

/-- Fiber ampleness is unchanged by passing to the base local ring. -/
theorem closedFiber_ample_iff (L : X.Modules) :
    AmpleLineBundle ((Scheme.Modules.pullback ((projection f s).fiberι
      (IsLocalRing.closedPoint (S.presheaf.stalk s)))).obj
        ((Scheme.Modules.pullback (toSource f s)).obj L)) ↔
        AmpleLineBundle ((Scheme.Modules.pullback (f.fiberι s)).obj L) := by
  constructor
  · intro h
    exact (ampleLineBundle_pullback_iso_iff _ _).mp
      (h.of_iso (closedFiberLineIso f s L).symm)
  · intro h
    exact (h.pullback_affine (closedFiberIso f s).hom).of_iso (closedFiberLineIso f s L)

end FLT.Mazur.StalkBase
