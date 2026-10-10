/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Ampleness on actual fibers after base change

The induced map of fibers is affine, being a base change of the residue
field map. Pullback composition identifies its line bundle with the
restriction of the pulled-back line to the new fiber.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

/-- Fiber ampleness is preserved by any cartesian base change. -/
theorem ampleLineBundle_fiber_of_isPullback {P X Y S : Scheme.{u}}
    {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (y : Y) (L : X.Modules)
    (hL : AmpleLineBundle ((pullback (f.fiberι (g y))).obj L)) :
    AmpleLineBundle ((pullback (q.fiberι y)).obj ((pullback p).obj L)) := by
  let k : q.fiber y ⟶ f.fiber (g y) :=
    Limits.pullback.map _ _ _ _ p (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)
  have hk : IsPullback k (q.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h y
  let _ : IsAffineHom k := MorphismProperty.of_isPullback hk.flip
    (inferInstance : IsAffineHom (Spec.map (g.residueFieldMap y)))
  have he : k ≫ f.fiberι (g y) = q.fiberι y ≫ p := by
    simp [k, Scheme.Hom.fiberι]
  exact (hL.pullback_affine k).of_iso
    ((pullbackComp (q.fiberι y) p).app L ≪≫
      (pullbackCongr he.symm).app L ≪≫ ((pullbackComp k (f.fiberι (g y))).app L).symm)

/-- Restricting the base preserves ampleness at the corresponding point of its fiber. -/
theorem ampleLineBundle_fiber_morphismRestrict {X S : Scheme.{u}}
    (f : X ⟶ S) (V : S.Opens) (s : V.toScheme) (L : X.Modules)
    (hL : AmpleLineBundle ((pullback (f.fiberι (V.ι s))).obj L)) :
    AmpleLineBundle ((pullback ((f ∣_ V).fiberι s)).obj
      ((pullback (f ⁻¹ᵁ V).ι).obj L)) :=
  ampleLineBundle_fiber_of_isPullback (isPullback_morphismRestrict f V).flip s L hL

end FLT.Mazur.FCurve
