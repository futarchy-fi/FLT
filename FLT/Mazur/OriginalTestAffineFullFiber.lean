/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber

/-!
# Original étale test neighborhoods meeting constructed affine full fibers

Intersect the constructed affine chart with an arbitrary original test and
its given Picard section. The actual intersection retains that section on
every test, and the specified whole geometric map lifts into its full fiber.
Only the chosen geometric fiber is asserted full, not an open neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
  {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ T)
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- The original test has an actual étale neighborhood retaining its section and a full fiber. -/
theorem exists_original_test_affine_full_fiber :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V),
      IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      ∃ (Y : Over (Spec (.of R))) (q : Y ⟶ T) (r : Y ⟶ A) (z : Over.mk t ⟶ Y),
        Etale q.left ∧ z ≫ q = b ∧
        (relativeFppfSheaf f).obj.map q.op s =
          (relativeFppfSheaf f).obj.map r.op (sectionAt f hL d V c k) ∧
        (z ≫ r).left η ∈ fullEnvelopeLocus f hL d V c k := by
  obtain ⟨d, V, c, A, k, a, hV, he, hA, hk, ha, hx⟩ :=
    exists_arbitrary_geometric_affine_full_fiber f hL t
      ((relativeFppfSheaf f).obj.map b.op s)
  let _ := he
  let _ := hk
  let O := variableHilbertOverlap f d V c T s
  let p : O ⟶ variableHilbertTest f d V := variableHilbertOverlapToChart f d hL V c T s
  let j : O ⟶ T := variableHilbertOverlapToTest f d V c T s
  have hac : variableHilbertPoint f d hL V c (Over.mk t) (a ≫ k) =
      (relativeFppfSheaf f).obj.map b.op s := by
    rw [← variableChartSection_map]
    simpa only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using ha
  obtain ⟨w, hw, _⟩ := variableHilbertOverlap_lift f d hL V c T s b (a ≫ k) hac
  let Y : Over (Spec (.of R)) := pullback p k
  let q : Y ⟶ T := pullback.fst p k ≫ j
  let r : Y ⟶ A := pullback.snd p k
  let z : Over.mk t ⟶ Y := pullback.lift w a hw.2
  have hzq : z ≫ q = b := by
    rw [← Category.assoc, pullback.lift_fst]
    exact hw.1
  have hzr : z ≫ r = a := pullback.lift_snd _ _ _
  have hj : Etale j.left := variableHilbertOverlapToTest_etale f d V T c s
  let _ := hj
  let _ : IsOpenImmersion (pullback.fst p k).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback p k).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion k.left))
  have hq : Etale q.left := inferInstanceAs (Etale ((pullback.fst p k).left ≫ j.left))
  refine ⟨d, V, c, A, k, hV, he, hA, hk, Y, q, r, z, hq, hzq, ?_, ?_⟩
  · have hc : (relativeFppfSheaf f).obj.map j.op s =
        (relativeFppfSheaf f).obj.map p.op (variableChartSection f hL d V c) := by
      rw [variableChartSection_map]
      exact (variableHilbertOverlap_class f d hL V c T s).symm
    change (relativeFppfSheaf f).obj.map (pullback.fst p k ≫ j).op s = _
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hc]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition]
    simp only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  · rwa [hzr]

end FLT.Mazur.HilbertChart.AffineRestriction
