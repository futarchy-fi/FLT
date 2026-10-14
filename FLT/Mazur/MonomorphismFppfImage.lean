/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismOpenImage
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Descending actual inverses from fppf neighborhoods

An actual lift of a flat, locally finitely presented neighborhood through a
monomorphism gives an inverse on its open image. The descent retains the whole
original scheme structure, so it applies to nonreduced neighborhoods as well.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismOpenImage
set_option backward.isDefEq.respectTransparency false
variable {D K Y : Scheme.{u}} (m : D ⟶ K) [Mono m]

/-- A section of a monomorphism gives an actual inverse, including on nilpotents. -/
def sectionIso (a : K ⟶ D) (ha : a ≫ m = 𝟙 K) : D ≅ K where
  hom := m
  inv := a
  hom_inv_id := by
    apply (cancel_mono m).mp
    rw [Category.assoc, ha, Category.comp_id, Category.id_comp]
  inv_hom_id := ha

/-- A lift after a genuine fppf cover proves the original comparison is an isomorphism. -/
theorem isIso_of_fppf_lift (t : Y ⟶ K) [Flat t] [LocallyOfFinitePresentation t]
    [Surjective t] (a : Y ⟶ D) (ha : a ≫ m = t) : IsIso m := by
  let b : Y ⟶ pullback m t := pullback.lift a (𝟙 _) (by simpa using ha)
  have hb : b ≫ pullback.snd m t = 𝟙 _ := pullback.lift_snd _ _ _
  let e := sectionIso (pullback.snd m t) b hb
  have hi : IsIso (pullback.snd m t) := e.isIso_hom
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hi

/-- The open image of an actual fppf neighborhood lift lies in the original inverse locus. -/
theorem fppf_image_le (t : Y ⟶ K) [Flat t] [LocallyOfFinitePresentation t]
    (a : Y ⟶ D) (ha : a ≫ m = t) :
    Set.range t ⊆ (locus m : Set K) := by
  let U : K.Opens := ⟨Set.range t, t.isOpenMap.isOpen_range⟩
  let t' : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι t (by simp [U])
  have ht : t' ≫ U.ι = t := IsOpenImmersion.lift_fac _ _ _
  let _ : Flat t' := MorphismProperty.of_postcomp (W := @Flat) (W' := @IsOpenImmersion) t' U.ι
    inferInstance (by rwa [ht])
  let _ : LocallyOfFinitePresentation t' := MorphismProperty.of_postcomp
    (W := @LocallyOfFinitePresentation) (W' := @IsOpenImmersion) t' U.ι
    inferInstance (by rwa [ht])
  let _ : Surjective t' := ⟨by
    rintro ⟨x, y, hy⟩
    refine ⟨y, ?_⟩
    apply U.ι.injective
    exact (congrArg (fun z ↦ z y) ht).trans hy⟩
  let b : Y ⟶ pullback m U.ι := pullback.lift a t' (ha.trans ht.symm)
  let _ : IsIso (pullback.snd m U.ι) := isIso_of_fppf_lift
    (pullback.snd m U.ι) t' b (pullback.lift_snd _ _ _)
  apply le_locus m U (inv (pullback.snd m U.ι) ≫ pullback.fst m U.ι)
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- Pointwise fppf lifts supply actual Zariski inverse neighborhoods in the same target. -/
theorem mem_locus_of_fppf_lift (t : Y ⟶ K) [Flat t] [LocallyOfFinitePresentation t]
    (a : Y ⟶ D) (ha : a ≫ m = t) (y : Y) : t y ∈ locus m :=
  fppf_image_le m t a ha ⟨y, rfl⟩

end FLT.Mazur.MonomorphismOpenImage
