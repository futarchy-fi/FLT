/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSmoothPullback
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The smooth-group comparison is an isomorphism

The smooth-locus base-change theorem shows that the canonical open
immersion from the pulled-back group onto the new smooth locus is surjective.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {S T : Scheme} (E : GeneralizedEllipticCurve S)

/-- The group inclusion has exactly the relative smooth locus as its range. -/
theorem inclusion_range : Set.range E.inclusion.left = E.curve.hom.smoothLocus := by
  have : IsIso E.smoothIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map E.smoothIso.hom))
  have hs : Function.Surjective E.smoothIso.hom.left := E.smoothIso.hom.left.homeomorph.surjective
  change Set.range (E.smoothIso.hom.left ≫ E.curve.hom.smoothLocus.ι) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hs.range_eq, Set.image_univ]
  exact Scheme.Opens.range_ι E.curve.hom.smoothLocus

variable (g : T ⟶ S)

/-- The pulled-back inclusion covers the entire new smooth locus. -/
theorem pullbackInclusion_range :
    Set.range (E.pullbackInclusion g).left = (E.pullbackCurve g).hom.smoothLocus := by
  have : Flat E.curve.hom := E.family.family.2.1
  change Set.range (pullback.map E.group.hom g E.curve.hom g
    E.inclusion.left (𝟙 T) (𝟙 S) (by simp) (by simp)) = _
  rw [Scheme.Pullback.range_map, E.inclusion_range]
  simp only [Scheme.Hom.id_base, TopCat.coe_id, Set.range_id, Set.preimage_univ,
    Set.inter_univ]
  exact congrArg (fun U : (E.pullbackCurve g).left.Opens ↦ (U : Set (E.pullbackCurve g).left))
    (E.curve.hom.preimage_smoothLocus_baseChange g)

/-- The canonical smooth-group comparison is surjective. -/
theorem smoothPullbackComparison_surjective :
    Function.Surjective (E.smoothPullbackComparison g).left := by
  intro x
  obtain ⟨y, hy⟩ : x.val ∈ Set.range (E.pullbackInclusion g).left := by
    rw [E.pullbackInclusion_range g]
    exact x.property
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have h := congrArg (fun f ↦ f.left) (E.smoothPullbackComparison_inclusion g)
  exact (congrArg (fun f ↦ f y) h).trans hy

/-- The canonical comparison is an isomorphism of schemes. -/
instance smoothPullbackComparison_left_isIso : IsIso (E.smoothPullbackComparison g).left := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨inferInstance, ⟨E.smoothPullbackComparison_surjective g⟩⟩

/-- The canonical comparison is an isomorphism over the new base. -/
instance smoothPullbackComparison_isIso : IsIso (E.smoothPullbackComparison g) := by
  have : IsIso ((Over.forget T).map (E.smoothPullbackComparison g)) :=
    inferInstanceAs (IsIso (E.smoothPullbackComparison g).left)
  exact isIso_of_reflects_iso (E.smoothPullbackComparison g) (Over.forget T)

/-- Identification of the pulled-back group with the actual new smooth open. -/
def smoothPullbackIso : E.pullbackGroup g ≅ curveSmoothOpen (E.pullbackCurve g) :=
  asIso (E.smoothPullbackComparison g)

/-- The isomorphism retains the specified inclusion into the pulled-back curve. -/
@[reassoc (attr := simp)]
theorem smoothPullbackIso_inclusion :
    (E.smoothPullbackIso g).hom ≫ curveSmoothInclusion (E.pullbackCurve g) =
      E.pullbackInclusion g := E.smoothPullbackComparison_inclusion g

end FLT.Mazur.GeneralizedEllipticCurve
