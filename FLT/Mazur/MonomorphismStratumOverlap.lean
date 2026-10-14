/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismGenericStratum

/-!
# Original-arrow compatibility on actual kernel-stratum overlaps

Two constructed exact images are compared using their actual scheme pullback.
The recovered original arrows agree there. This overlap is also the pullback
over the original source, without reducing its possibly nonreduced structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.MonomorphismGenericStratum
set_option backward.isDefEq.respectTransparency false
variable {D K : Scheme.{0}} (m : D ⟶ K) [Mono m] [QuasiCompact m]
  [LocallyOfFinitePresentation m] [IsAffine K]
  (P Q : Ideal Γ(K, ⊤)) [P.IsPrime] [Q.IsPrime]

/-- The actual image inclusion into the original kernel, with all coefficient maps retained. -/
def imageToTarget : (imageOpen m P).toScheme ⟶ K :=
  (imageOpen m P).ι ≫ targetMap m P ≫ stratumMap P

/-- The two independent image patches retain the same original arrow on their whole overlap. -/
@[reassoc]
theorem imageOverlap_original :
    pullback.fst (imageToTarget m P) (imageToTarget m Q) ≫ imageToOriginal m P =
      pullback.snd (imageToTarget m P) (imageToTarget m Q) ≫ imageToOriginal m Q := by
  apply (cancel_mono m).mp
  rw [Category.assoc, Category.assoc, imageToOriginal_comp, imageToOriginal_comp]
  exact pullback.condition

/-- The overlap over the candidate kernel is exactly the overlap over the original source. -/
def imageOverlapIso : pullback (imageToTarget m P) (imageToTarget m Q) ≅
    pullback (imageToOriginal m P) (imageToOriginal m Q) where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (imageOverlap_original m P Q)
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    have h := congrArg (fun t ↦ t ≫ m)
      (pullback.condition (f := imageToOriginal m P) (g := imageToOriginal m Q))
    simpa only [Category.assoc, imageToOriginal_comp, imageToTarget] using h)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- The comparison keeps the first original image chart. -/
@[reassoc]
theorem imageOverlapIso_fst : (imageOverlapIso m P Q).hom ≫
    pullback.fst (imageToOriginal m P) (imageToOriginal m Q) =
      pullback.fst (imageToTarget m P) (imageToTarget m Q) :=
  pullback.lift_fst _ _ _

/-- The independent second image chart is retained as well. -/
@[reassoc]
theorem imageOverlapIso_snd : (imageOverlapIso m P Q).hom ≫
    pullback.snd (imageToOriginal m P) (imageToOriginal m Q) =
      pullback.snd (imageToTarget m P) (imageToTarget m Q) :=
  pullback.lift_snd _ _ _

/-- Compatibility holds on arbitrary scheme tests, including nonreduced overlap tests. -/
theorem image_original_eq_of_target_eq {Z : Scheme}
    (a : Z ⟶ (imageOpen m P).toScheme) (b : Z ⟶ (imageOpen m Q).toScheme)
    (h : a ≫ imageToTarget m P = b ≫ imageToTarget m Q) :
    a ≫ imageToOriginal m P = b ≫ imageToOriginal m Q := by
  apply (cancel_mono m).mp
  simpa only [Category.assoc, imageToOriginal_comp, imageToTarget] using h

end FLT.Mazur.MonomorphismGenericStratum
