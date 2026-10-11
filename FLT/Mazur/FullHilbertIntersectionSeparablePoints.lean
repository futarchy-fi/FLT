/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothFiberSeparablePoints
public import FLT.Mazur.BaseMarkedHilbertFullIntersection

/-!
# Separable translation representatives of the original Picard class

Selecting a point in the nonempty full intersection preserves the original
class. Only its translation descends to the relative separable closure;
its Hilbert parameter is allowed to remain over the geometric field.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [IsSepClosed K] [Algebra k K]
  [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V)) (φ : R →+* k)

/-- A point in the full intersection gives the same class with a separable translation. -/
theorem exists_fullHilbert_separable_point
    (s : (relativeFppfSheaf f).obj.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))))))
    (hne : Nonempty (variableHilbertOverlap f d V c
      (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)))) s).left) :
    ∃ (y : Spec (.of (separableClosure k K)) ⟶ V.left)
      (p : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶
        variableHilbertTest f d V),
      y ≫ V.hom = Spec.map
        (CommRingCat.ofHom ((algebraMap k (separableClosure k K)).comp φ)) ∧
      p.left ≫ (variableHilbertBase f d V).left =
        Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K)) ≫ y ∧
      variableHilbertPoint f d hL V c _ p = s := by
  let T := Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)))
  let I := variableHilbertOverlap f d V c T s
  let j := variableHilbertOverlapArrow f d V c T s
  let t := variableHilbertOverlapToTest f d V c T s
  have H : IsPullback (prod.snd : prod T V ⟶ V).left
      (prod.fst : prod T V ⟶ T).left V.hom T.hom :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T V)).flip
  obtain ⟨y, z, hy, hzt, hzy⟩ := SmoothFiberSeparablePoints.exists_point V.hom φ
    (prod.snd : prod T V ⟶ V).left (prod.fst : prod T V ⟶ T).left H j.left hne
  have hz : z ≫ t.left = 𝟙 _ := hzt
  let u : T ⟶ I := Over.homMk z (by
    rw [← Over.w t, ← Category.assoc, hz]
    exact Category.id_comp T.hom)
  have hu : u ≫ t = 𝟙 T := Over.OverMorphism.ext hz
  refine ⟨y, u ≫ variableHilbertOverlapToChart f d hL V c T s, hy, ?_, ?_⟩
  · change z ≫ (variableHilbertOverlapToChart f d hL V c T s).left ≫ _ = _
    rw [← Over.comp_left, variableHilbertOverlapToChart_base]
    exact hzy
  · rw [variableHilbertPoint_natural, variableHilbertOverlap_class,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hu]
    change ((relativeFppfSheaf f).obj.map (𝟙 (op T))) s = s
    rw [CategoryTheory.Functor.map_id]
    rfl

end FLT.Mazur.HilbertChart
