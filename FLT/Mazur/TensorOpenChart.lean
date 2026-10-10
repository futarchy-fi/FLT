/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Actual tensor charts in a base-changed scheme

An affine chart over a coefficient ring gives an actual tensor chart in the
geometric base change. Its square with the original chart is cartesian.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (i : Spec (.of A) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
open scoped TensorProduct

/-- The tensor spectrum projects to the original affine chart. -/
def projection : Spec (.of (S ⊗[R] A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom
    (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)))

/-- The tensor chart embeds in the actual categorical base change. -/
def chart : Spec (.of (S ⊗[R] A)) ⟶
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) f :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
    (projection ≫ i) (by
      rw [Category.assoc, hi]
      rw [projection, ← pullbackSpecIso_inv_fst' R S A, ← pullbackSpecIso_inv_snd R S A]
      simp only [Category.assoc, pullback.condition])

/-- The new chart retains its coefficient structure. -/
@[reassoc] theorem chart_fst : chart f i hi ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) := pullback.lift_fst _ _ _

/-- The other projection retains every original chart function. -/
@[reassoc] theorem chart_snd : chart (S := S) f i hi ≫ pullback.snd _ _ =
    projection ≫ i := pullback.lift_snd _ _ _

/-- The explicit tensor chart is the pullback of the original chart. -/
theorem chart_isPullback : IsPullback (chart f i hi) (projection (R := R))
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) f) i := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := f) _
    (chart_snd f i hi) (.of_hasPullback _ _)
  rw [chart_fst, hi]
  exact IsPullback.of_iso_pullback ⟨by
    rw [projection, ← pullbackSpecIso_inv_fst' R S A, ← pullbackSpecIso_inv_snd R S A]
    simp only [Category.assoc, pullback.condition]⟩
      (pullbackSpecIso R S A).symm (pullbackSpecIso_inv_fst' R S A)
        (pullbackSpecIso_inv_snd R S A)

instance chart_isOpenImmersion [IsOpenImmersion i] :
    IsOpenImmersion (chart (S := S) f i hi) :=
  MorphismProperty.of_isPullback (chart_isPullback f i hi).flip inferInstance

end FLT.Mazur.TensorOpenChart
