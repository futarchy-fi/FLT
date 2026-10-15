/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricOrderedAllLiftTranslation
public import FLT.Mazur.FiniteGeometricEtaleTranslations

/-!
# Common original étale translations controlling all independent lifts

Finitely many arbitrary geometric classes share one degree and one
constructed original affine étale parameter scheme. Each input class has
its own translation on that common test, valid at every independent K-lift.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R k K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : AmpleLineBundle B)
  (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]
  {n : ℕ} (s : Fin n → (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := K) t)))

include hB in
/-- One common original affine étale test controls all lifts of every independent input class. -/
theorem exists_finite_all_lift_translations :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : Fin n → (relativeFppfSheaf f).obj.obj (op V))
      (_z : coefficientTest (K := K) t ⟶ V), IsAffine V.left ∧ Etale V.hom ∧
      ∀ (w : coefficientTest (K := K) t ⟶ V) j,
        s j * (relativeFppfSheaf f).obj.map w.op (c j) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t)) := by
  let iL : AlgebraicClosure k →ₐ[k] K := IsAlgClosed.lift
  let _ := iL.toRingHom.toAlgebra
  let _ : IsScalarTower k (AlgebraicClosure k) K :=
    IsScalarTower.of_algebraMap_eq' iL.comp_algebraMap.symm
  let T := coefficientTest (K := K) t
  obtain ⟨d, i, v, hv⟩ := exists_simultaneous_smooth_acyclic_degree f hB T.hom s
  have h (j : Fin n) := exists_transcendental_ordered_translation_of_acyclicity
    (L := AlgebraicClosure k) f hB t (i j) d (s j) (v j) (hv j)
  choose E r z hE he hall using h
  let _ (j : Fin n) : Etale (E j).hom := he j
  obtain ⟨V, q, w, a, hV, hq, hw, ha, _⟩ :=
    EtaleFiniteGeometricDiagram.exists_common_affine (fun j ↦ (E j).left)
      (fun j ↦ (E j).hom) T.hom (fun j ↦ (z j).left) (fun j ↦ (z j).w)
  let W : Over (Spec (.of R)) := Over.mk q
  let w' : T ⟶ W := Over.homMk w hw
  let a' (j : Fin n) : W ⟶ E j := Over.homMk (a j) (ha j)
  let c (j : Fin n) := (relativeFppfSheaf f).obj.map (a' j ≫ r j).op
    (smoothTranslationClass f hB.2.1 (i j))
  refine ⟨d, W, c, w', hV, hq, fun l j ↦ ?_⟩
  have h := hall j (l ≫ a' j)
  simpa only [c, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Category.assoc] using h

end FLT.Mazur.HilbertChart
