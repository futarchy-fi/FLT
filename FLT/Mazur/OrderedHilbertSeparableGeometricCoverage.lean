/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FullHilbertIntersectionSeparablePoints
public import FLT.Mazur.SmoothHilbertTestCover

/-!
# Original geometric Picard classes have separable ordered translations

The fixed smooth chart family covers every geometric class. Re-selecting
inside its full intersection makes the translation separable and retains
the same original class, with unrestricted geometric Hilbert parameters.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
  [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (φ : R →+* k)

/-- Every original geometric class has an ordered representative with separable translation. -/
theorem exists_orderedHilbert_separable_geometric_point
    (s : (relativeFppfSheaf f).obj.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)))))) :
    ∃ (i : SmoothHilbertTranslationIndex)
      (y : Spec (.of (separableClosure k K)) ⟶ (smoothTranslationTest f i.1).left)
      (p : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶
        smoothHilbertTest f i),
      y ≫ (smoothTranslationTest f i.1).hom = Spec.map
        (CommRingCat.ofHom ((algebraMap k (separableClosure k K)).comp φ)) ∧
      p.left ≫ (variableHilbertBase f i.2 (smoothTranslationTest f i.1)).left =
        Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K)) ≫ y ∧
      smoothHilbertPoint f hL i _ p = s := by
  let T := Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)))
  obtain ⟨i, q, _⟩ := smoothHilbertOverlap_geometric_lift f hL T s (𝟙 _)
  obtain ⟨y, p, hy, hp, hc⟩ := exists_fullHilbert_separable_point f hL i.2
    (smoothTranslationTest f i.1) (smoothTranslationClass f hL.2.1 i.1) φ s
    ⟨q default⟩
  exact ⟨i, y, p, hy, hp, hc⟩

end FLT.Mazur.HilbertChart
