/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineOpenClosedDescent

/-!
# Closed immersion descent on a finite affine target cover

When the inverse images of a finite affine cover are affine at a stage,
closedness on the inverse limit descends simultaneously and glues on the target.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]

include hc in
/-- Closedness descends when an affine target cover has affine inverse images. -/
theorem exists_isClosedImmersion_of_affine_preimages (i : I)
    {Y : Scheme.{u}} (f : D.obj i ⟶ Y) [LocallyOfFiniteType f]
    [IsClosedImmersion (c.π.app i ≫ f)]
    {K : Type v} [Finite K] (V : K → Y.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (ha : ∀ k, IsAffineOpen (V k))
    (hi : ∀ k, IsAffineOpen (f ⁻¹ᵁ V k)) :
    ∃ (j : I) (g : j ⟶ i), IsClosedImmersion (D.map g ≫ f) := by
  let _ (k : K) : IsAffine (V k).toScheme := ha k
  have hl (k : K) : IsClosedImmersion ((c.π.app i ∣_ f ⁻¹ᵁ V k) ≫ (f ∣_ V k)) := by
    rw [← morphismRestrict_comp]
    exact IsZariskiLocalAtTarget.restrict
      (inferInstanceAs (IsClosedImmersion (c.π.app i ≫ f))) (V k)
  obtain ⟨j, g, hg⟩ := exists_isClosedImmersion_on_affineOpens D c hc i
    (fun k ↦ f ⁻¹ᵁ V k) hi (fun k ↦ (V k).toScheme) (fun k ↦ f ∣_ V k) hl
  refine ⟨j, g, IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) V hV ?_⟩
  intro k
  rw [morphismRestrict_comp]
  exact hg k

end FLT.Mazur.Approximation
