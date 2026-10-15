/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranscendentalOrderedAllLiftTranslation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Original all-lift translations for arbitrary geometric Picard classes

Embed an algebraic closure of the original residue field into the given
geometric coefficient field. The detecting-open construction then supplies
one original translation valid at every independent lift. Neither the
class nor the geometric coefficient field is assumed algebraic over k.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : AmpleLineBundle B)
  (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]

/-- Every arbitrary geometric class has an original ordered translation controlling all lifts. -/
theorem exists_geometric_ordered_all_lift_translation
    (s : (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := K) t))) :
    ∃ (j : SmoothTranslationIndex) (d : ℕ) (E : Over (Spec (.of R)))
      (r : E ⟶ smoothTranslationTest f j) (_z : coefficientTest (K := K) t ⟶ E),
      IsAffine E.left ∧ Etale E.hom ∧
      ∀ w : coefficientTest (K := K) t ⟶ E,
        s * (relativeFppfSheaf f).obj.map w.op
          ((relativeFppfSheaf f).obj.map r.op (smoothTranslationClass f hB.2.1 j)) ∈
            (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t)) := by
  let i : AlgebraicClosure k →ₐ[k] K := IsAlgClosed.lift
  let _ := i.toRingHom.toAlgebra
  let _ : IsScalarTower k (AlgebraicClosure k) K :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  exact exists_transcendental_ordered_all_lift_translation
    (L := AlgebraicClosure k) f hB t s

end FLT.Mazur.HilbertChart
