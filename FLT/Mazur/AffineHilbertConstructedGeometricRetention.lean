/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertGeometricOrbitRetention
public import FLT.Mazur.AffineHilbertGeometricAcyclicFiber

/-!
# Original affine full fibers with constructed chart retention

When all geometric translations have acyclic divisors of the fixed degree,
construct one original affine chart containing every parameter. Its full
original envelope fiber contains the supplied class. Retention is now an
output; simultaneous acyclicity remains an explicit geometric condition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {K : Type} [Field K] [IsSepClosed K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) (v : Over.mk t ⟶ V)
local notation "η" => (default : Spec (CommRingCat.of K))

/-- Simultaneous acyclicity constructs affine retention and a full original envelope fiber. -/
theorem exists_affine_full_fiber_of_geometric_acyclicity
    (hA : ∀ w : Over.mk t ⟶ V, s * (relativeFppfSheaf f).obj.map w.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t))) :
    ∃ (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A),
      IsAffine A.left ∧ ∃ hk : IsOpenImmersion k.left,
      let _ := hk
      b ≫ k = acyclicTranslationLift f hL d V c s v (hA v) ∧
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeLocus f hL d V c k := by
  let a := acyclicTranslationLift f hL d V c s v (hA v)
  obtain ⟨W, hW, haW, hret⟩ :=
    exists_affine_retaining_geometric_class f hL d V c a
  let A : Over (Spec (.of R)) := Over.mk (W.ι ≫ (variableHilbertTest f d V).hom)
  let k : A ⟶ variableHilbertTest f d V := Over.homMk W.ι
  let _ : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hr : Set.range a.left ⊆ Set.range W.ι := by
    simpa only [Scheme.Opens.range_ι] using haW
  let b₀ := IsOpenImmersion.lift W.ι a.left hr
  have hb₀ : b₀ ≫ W.ι = a.left := IsOpenImmersion.lift_fac _ _ _
  let b : Over.mk t ⟶ A := Over.homMk b₀ (by
    change b₀ ≫ W.ι ≫ (variableHilbertTest f d V).hom = t
    rw [← Category.assoc, hb₀, a.w]
    rfl)
  have hb : b ≫ k = a := Over.OverMorphism.ext hb₀
  have hc : (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s := by
    change (relativeFppfSheaf f).obj.map b.op
      ((relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d V c)) = s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hb]
    exact acyclicTranslationLift_class f hL d V c s v (hA v)
  have hA' (w : Over.mk t ⟶ V) :
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) *
        (relativeFppfSheaf f).obj.map w.op c ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
    rw [hc]
    exact hA w
  refine ⟨A, k, b, hW, inferInstanceAs (IsOpenImmersion W.ι), hb, hc, ?_⟩
  apply fullEnvelopeLocus_of_all_geometric_translations f hL d V c k b hA'
  intro w
  change (acyclicTranslationLift f hL d V c _ w (hA' w)).left η ∈ Set.range W.ι
  rw [Scheme.Opens.range_ι]
  apply hret _ _ ⟨η, rfl⟩
  rw [acyclicTranslationLift_class, hc, acyclicTranslationLift_class]

end FLT.Mazur.HilbertChart.AffineRestriction
