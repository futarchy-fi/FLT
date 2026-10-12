/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGroupPointedRigidity

/-!
# Pointed morphisms from proper integral groups preserve multiplication

Apply rigidity to the quotient of the two candidate multiplication maps.
The source's two unit laws make that quotient trivial on both axes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
namespace FLT.Mazur

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Preserving the origin forces a morphism from a proper integral group to be a group map. -/
theorem properGroup_isMonHom_of_one {K : Type u} [Field K] [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [GrpObj G] [GrpObj Z]
    [IsProper G.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    [IsIntegral (G ⊗ G).left]
    (f : G ⟶ Z) (hf : η[G] ≫ f = η[Z]) : IsMonHom f := by
  let d : G ⊗ G ⟶ Z := (μ[G] ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hl : η[G] ▷ G ≫ d = 1 := by
    simp only [d, GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc,
      MonObj.one_mul, whiskerRight_fst, whiskerRight_snd]
    simp only [Category.assoc, hf, leftUnitor_hom]
    rw [show fst (𝟙_ (Over (Spec (.of K)))) G ≫ η[Z] = 1 from
      congrArg (fun t ↦ t ≫ η[Z]) (toUnit_unique _ _)]
    simp
  have hr : G ◁ η[G] ≫ d = 1 := by
    simp only [d, GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc,
      MonObj.mul_one, whiskerLeft_fst, whiskerLeft_snd]
    simp only [Category.assoc, hf, rightUnitor_hom]
    rw [show snd G (𝟙_ (Over (Spec (.of K)))) ≫ η[Z] = 1 from
      congrArg (fun t ↦ t ≫ η[Z]) (toUnit_unique _ _)]
    simp
  have hd : d = 1 := properGroup_eq_one_of_axes G Z d hl hr
  refine ⟨hf, ?_⟩
  have hm := div_eq_one.mp hd
  change μ[G] ≫ f = (fst G G ≫ f) * (snd G G ≫ f) at hm
  rw [CategoryTheory.Hom.mul_def] at hm
  have ht : lift (fst G G ≫ f) (snd G G ≫ f) = f ⊗ₘ f := by
    ext <;> simp
  rwa [ht] at hm

end FLT.Mazur
