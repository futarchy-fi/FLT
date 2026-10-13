/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# A finite etale morphism covers its actual open-and-closed image

Restrict the target to the actual image. The resulting map is finite etale
and surjective, hence an actual fppf cover, with the same entire source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FiniteEtaleImageCover
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsFinite f]

/-- The actual image, open because the original map is etale. -/
def imageOpen : Y.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩

/-- Finiteness also makes this same image closed. -/
theorem imageOpen_isClosed : IsClosed (imageOpen f : Set Y) := by
  exact f.isClosedMap.isClosed_range

/-- The coefficient image is a closed subscheme as well as an open subscheme. -/
instance imageOpen_ι_isClosedImmersion : IsClosedImmersion (imageOpen f).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact imageOpen_isClosed f

instance imageOpen_isAffine [IsAffine Y] : IsAffine (imageOpen f) :=
  isAffine_of_isAffineHom (imageOpen f).ι

/-- Factor the original morphism through its entire image. -/
def cover : X ⟶ imageOpen f :=
  IsOpenImmersion.lift (imageOpen f).ι f (by simp [imageOpen])

omit [IsFinite f] in
/-- This factorization preserves the original scheme and structure-sheaf morphism. -/
@[reassoc]
theorem cover_ι : cover f ≫ (imageOpen f).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

instance cover_surjective : Surjective (cover f) := by
  constructor
  rintro ⟨y, z, hz⟩
  refine ⟨z, ?_⟩
  apply (imageOpen f).ι.isOpenEmbedding.injective
  change ((cover f) ≫ (imageOpen f).ι) z = y
  rw [cover_ι]
  exact hz

instance cover_etale : Etale (cover f) := by
  have : Etale (cover f ≫ (imageOpen f).ι) := by rw [cover_ι]; infer_instance
  exact Etale.of_comp (cover f) (imageOpen f).ι

instance cover_isFinite : IsFinite (cover f) := by
  have : IsFinite (cover f ≫ (imageOpen f).ι) := by rw [cover_ι]; infer_instance
  exact IsFinite.of_comp (cover f) (imageOpen f).ι

omit [IsFinite f] in
/-- Every original point has an actual point of the finite etale image cover. -/
theorem cover_point (x : X) : (imageOpen f).ι (cover f x) = f x :=
  congrArg (fun g : X ⟶ Y ↦ g x) (cover_ι f)

end FLT.Mazur.FiniteEtaleImageCover
