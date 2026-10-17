/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphScheme
public import FLT.Mazur.PolygonTopNodeGraphFlat

/-!
# The full source projection of a preserving node graph is invertible

Preservation identifies the actual graph algebra with the original node
subalgebra. The original source map is consequently bijective, and its
spectrum is an isomorphism over the entire original node input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] topNodeGraphAlgebra
variable (R : Type) [CommRing R] (m : ℕ)
  (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
variable (hp : ∀ p : (Ring R (m + 1))[T;T⁻¹] × (Ring R (m + 1))[T;T⁻¹],
  p ∈ stageNodeBranchSubalgebra R (m + 1) →
    stageNodeBranchSubstitution R (m + 1) u v p ∈ stageNodeBranchSubalgebra R (m + 1))
include hp

/-- Preservation makes the unchanged source map bijective on all original node functions. -/
theorem topNodeGraphSource_bijective_of_preserves :
    Function.Bijective (topNodeGraphSource R m u v) := by
  constructor
  · intro x y he
    apply stageNodeBranchPair_injective R (m + 1)
    exact congrArg Subtype.val he
  · intro z
    have hz : z.val ∈ stageNodeBranchSubalgebra R (m + 1) :=
      ((topNodeGraphAlgebra_eq_source_iff R m u v).mpr hp).le z.property
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩

/-- The actual source projection is an isomorphism onto the whole original node. -/
theorem topNodeGraphSchemeSource_isIso_of_preserves :
    IsIso (topNodeGraphSchemeSource R m u v) := by
  let e := RingEquiv.ofBijective (topNodeGraphSource R m u v).toRingHom
    (topNodeGraphSource_bijective_of_preserves R m u v hp)
  change IsIso (Spec.map (CommRingCat.ofHom e.toRingHom))
  let _ : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (show IsIso e.toCommRingCatIso.hom from inferInstance)
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
