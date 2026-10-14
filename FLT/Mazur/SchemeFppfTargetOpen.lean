/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatTargetOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Actual fppf projections inside the original target

The image of the whole flat restriction is open. Factoring through this image
gives a flat, surjective, locally finitely presented projection, with a proved
Cartesian square back to the original source. Global flatness and surjectivity
of the original map are not hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfTargetOpen
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- The complete source over the maximal flat target open. -/
def source : Scheme.{u} := pullback f (SchemeFlatTargetOpen.locus f).ι

/-- Its actual map to the unchanged target. -/
def map : source f ⟶ Y :=
  SchemeFlatTargetOpen.projection f ≫ (SchemeFlatTargetOpen.locus f).ι

instance map_flat : Flat (map f) := inferInstanceAs (Flat (_ ≫ _))

instance map_locallyOfFinitePresentation : LocallyOfFinitePresentation (map f) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _ ≫ _))

/-- Remove empty fibers using the open image of the actual flat projection. -/
def locus : Y.Opens := ⟨Set.range (map f), (map f).isOpenMap.isOpen_range⟩

/-- The unchanged complete source maps onto this open. -/
def projection : source f ⟶ (locus f).toScheme :=
  IsOpenImmersion.lift (locus f).ι (map f) (by simp [locus])

@[reassoc]
theorem projection_ι : projection f ≫ (locus f).ι = map f :=
  IsOpenImmersion.lift_fac _ _ _

instance projection_flat : Flat (projection f) :=
  MorphismProperty.of_postcomp (W := @Flat) (W' := @IsOpenImmersion)
    (projection f) (locus f).ι inferInstance (by rw [projection_ι]; infer_instance)

instance projection_locallyOfFinitePresentation : LocallyOfFinitePresentation (projection f) :=
  MorphismProperty.of_postcomp
    (W := @LocallyOfFinitePresentation) (W' := @IsOpenImmersion)
    (projection f) (locus f).ι inferInstance (by rw [projection_ι]; infer_instance)

instance projection_surjective : Surjective (projection f) := ⟨by
  rintro ⟨y, x, hx⟩
  refine ⟨x, ?_⟩
  apply (locus f).ι.injective
  exact (congrArg (fun z ↦ z x) (projection_ι f)).trans hx⟩

/-- The fppf region lies in the whole-source flat target open. -/
theorem locus_le_flat : locus f ≤ SchemeFlatTargetOpen.locus f := by
  rintro y ⟨x, rfl⟩
  exact (SchemeFlatTargetOpen.projection f x).property

/-- The Cartesian square certifies that every original point and nilpotent is retained. -/
theorem isPullback : IsPullback
    (pullback.fst f (SchemeFlatTargetOpen.locus f).ι) (projection f) f (locus f).ι := by
  let i := Y.homOfLE (locus_le_flat f)
  have hi : i ≫ (SchemeFlatTargetOpen.locus f).ι = (locus f).ι :=
    Y.homOfLE_ι (locus_le_flat f)
  have hp : projection f ≫ i = SchemeFlatTargetOpen.projection f := by
    apply (cancel_mono (SchemeFlatTargetOpen.locus f).ι).mp
    rw [Category.assoc, hi, projection_ι]
    rfl
  have h := IsPullback.of_horiz_isIso_mono
    (show CommSq (𝟙 (source f)) (projection f) (SchemeFlatTargetOpen.projection f) i from
      ⟨by rw [Category.id_comp, hp]⟩)
  have H := h.paste_horiz (IsPullback.of_hasPullback f (SchemeFlatTargetOpen.locus f).ι)
  simpa only [Category.id_comp, hi] using H

/-- In particular the literal pullback of the original source has a surjective projection. -/
theorem pullback_surjective : Surjective (pullback.snd f (locus f).ι) := by
  rw [← (isPullback f).isoPullback_inv_snd]
  infer_instance

/-- Pointwise, this is the actual image intersected with the whole-source flat locus. -/
theorem coe_locus : (locus f : Set Y) =
    Set.range f ∩ (SchemeFlatTargetOpen.locus f : Set Y) := by
  change Set.range (pullback.snd f (SchemeFlatTargetOpen.locus f).ι ≫
    (SchemeFlatTargetOpen.locus f).ι) = _
  rw [Scheme.Pullback.range_snd_comp, Scheme.Opens.range_ι]

/-- A smaller retained open is covered by its complete original inverse image. -/
theorem surjective_of_le (U : Y.Opens) (hU : U ≤ locus f) :
    Surjective (pullback.snd f U.ι) := by
  constructor
  intro y
  have hy : y.val ∈ Set.range f := by
    have hy := hU y.property
    rw [← SetLike.mem_coe, coe_locus] at hy
    exact hy.1
  have hy' : y ∈ Set.range (pullback.snd f U.ι) := by
    rw [Scheme.Pullback.range_snd]
    exact hy
  exact hy'

/-- This is the largest open admitting an actual fppf whole-source projection. -/
theorem le_locus_iff (U : Y.Opens) : U ≤ locus f ↔
    Flat (pullback.snd f U.ι) ∧ Surjective (pullback.snd f U.ι) := by
  constructor
  · intro hU
    exact ⟨SchemeFlatTargetOpen.flat_of_le f U (hU.trans (locus_le_flat f)),
      surjective_of_le f U hU⟩
  · rintro ⟨hf, hs⟩ y hy
    rw [← SetLike.mem_coe, coe_locus]
    refine ⟨?_, (SchemeFlatTargetOpen.le_locus_iff f U).mpr hf hy⟩
    obtain ⟨z, hz⟩ := hs.1 ⟨y, hy⟩
    refine ⟨pullback.fst f U.ι z, ?_⟩
    have he := congrArg (fun t ↦ t z) (pullback.condition (f := f) (g := U.ι))
    change f (pullback.fst f U.ι z) = U.ι (pullback.snd f U.ι z) at he
    rw [he, hz]
    rfl

end FLT.Mazur.SchemeFppfTargetOpen
