/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCurveFixedPointTranslation
public import FLT.Mazur.GroupObjectTranslationNaturality
public import FLT.Mazur.SmoothCurveDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Translation identification over the original field

Apply the group-curve fixed-point argument over the algebraic closure.
Normalization commutes with base change, and faithful pullback descends its
identity to the original group scheme and field.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {G : Over (Spec (.of K))} [GrpObj G]
  [IsProper G.hom] [GeometricallyIntegral G.hom] [SmoothOfRelativeDimension 1 G.hom]
  (e : G ≅ G)

/-- Geometric fixed-point freeness identifies the actual automorphism over its original field. -/
theorem geometricFixedPointFree_eq_translation
    (hf : ∀ (T : Scheme.{u}) [Nonempty T] (q : T ⟶ G.left), q ≫ e.hom.left ≠ q) :
    e.hom = translation ((1 : 𝟙_ (Over (Spec (.of K))) ⟶ G) ≫ e.hom) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let F := Over.pullback s
  let G' := F.obj G
  let _ : GrpObj G' := Functor.grpObjObj
  let _ : IsProper G'.hom := by dsimp [G', F]; infer_instance
  let _ : IsIntegral G'.left := by dsimp [G', F]; infer_instance
  let _ : SmoothOfRelativeDimension 1 G'.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom s) inferInstance
  have hd : topologicalKrullDim G'.left ≤ 1 :=
    le_of_eq (FCurve.smoothCurveDimension G'.hom inferInstance inferInstance)
  have he := fixedPointFree_eq_translation hd (F.mapIso e) (by
    intro q hq
    apply hf (Spec (.of (AlgebraicClosure K))) (q.left ≫ pullback.fst G.hom s)
    have hh := congrArg (fun f ↦ f.left ≫ pullback.fst G.hom s) hq
    simpa only [Over.comp_left, Functor.mapIso_hom, F, Over.pullback_map_left,
      Category.assoc, pullback.lift_fst] using hh)
  have hn := (eq_translation_iff (F.mapIso e)).mp he
  apply (eq_translation_iff e).mpr
  apply F.map_injective
  rw [map_normalizedIso, F.map_id]
  exact hn

end FLT.Mazur.GroupObjectPointTranslation
