/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SimultaneousEtaleAcyclicNeighborhood

/-!
# One original étale translation for a global original Picard section

A section on the unchanged coefficient base constructs one affine étale
translation class of fixed degree. The acyclic condition holds on its
whole source, and therefore on all independent geometric lifts at once.
A geometric class not extending to the original base is not covered here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (s : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))

include hL in
/-- One constructed original affine étale translation works on every independent geometric lift. -/
theorem exists_globalPicard_etale_acyclic_translation :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V)) (v : Over.mk t ⟶ V),
      IsAffine V.left ∧ Etale V.hom ∧
      ∀ w : Over.mk t ⟶ V,
        (relativeFppfSheaf f).obj.map (Over.homMk t).op s *
          (relativeFppfSheaf f).obj.map w.op c ∈
            (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  let T := Over.mk (𝟙 (Spec (.of R)))
  let _ : IsAffine T.left := inferInstanceAs (IsAffine (Spec (.of R)))
  let b : Over.mk t ⟶ T := Over.homMk t
  obtain ⟨d, i, V, q, v, r, hV, hq, _, hr⟩ :=
    exists_simultaneous_etale_acyclic_neighborhood f hL (T := T) (fun _ : Fin 1 ↦ s) b
  have hqhom : q.left = V.hom := (Category.comp_id q.left).symm.trans q.w
  let c := (relativeFppfSheaf f).obj.map (r 0).op (smoothTranslationClass f hL.2.1 (i 0))
  refine ⟨d, V, c, v, hV, hqhom ▸ hq, fun w ↦ ?_⟩
  have hwq : w ≫ q = b := by
    apply Over.OverMorphism.ext
    change w.left ≫ q.left = t
    rw [hqhom]
    exact w.w
  have h := (acyclicDegreePicardSubfunctor f d).map w.op (hr 0)
  change (relativeFppfSheaf f).obj.map w.op
    ((relativeFppfSheaf f).obj.map q.op s * c) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) at h
  simpa only [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hwq]
    using h

end FLT.Mazur.HilbertChart
