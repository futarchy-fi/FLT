/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine fiber opens under base change

The induced morphism of scheme fibers is affine because it is base change
of a morphism of residue-field spectra. This transports affineness of
restricted generator opens, including after shrinking the base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.Approximation

/-- Affineness of an open on a fiber persists under arbitrary base change. -/
theorem isAffineOpen_fiber_preimage_of_isPullback {P X Y S : Scheme.{u}}
    {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (y : Y) (U : X.Opens)
    (hU : IsAffineOpen (f.fiberι (g y) ⁻¹ᵁ U)) :
    IsAffineOpen (q.fiberι y ⁻¹ᵁ (p ⁻¹ᵁ U)) := by
  let k : q.fiber y ⟶ f.fiber (g y) :=
    pullback.map _ _ _ _ p (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)
  have hk : IsPullback k (q.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h y
  let _ : IsAffineHom k := MorphismProperty.of_isPullback hk.flip
    (inferInstance : IsAffineHom (Spec.map (g.residueFieldMap y)))
  have he : k ≫ f.fiberι (g y) = q.fiberι y ≫ p := by
    simp [k, Scheme.Hom.fiberι]
  have ha := hU.preimage k
  rwa [← Scheme.Hom.comp_preimage, he, Scheme.Hom.comp_preimage] at ha

/-- Restricting the base preserves affine inverse-image opens on its actual point fibers. -/
theorem isAffineOpen_fiber_preimage_morphismRestrict {X S : Scheme.{u}}
    (f : X ⟶ S) (V : S.Opens) (s : V.toScheme) (U : X.Opens)
    (hU : IsAffineOpen (f.fiberι (V.ι s) ⁻¹ᵁ U)) :
    IsAffineOpen ((f ∣_ V).fiberι s ⁻¹ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ U)) :=
  isAffineOpen_fiber_preimage_of_isPullback (isPullback_morphismRestrict f V).flip s U hU

end FLT.Mazur.Approximation
