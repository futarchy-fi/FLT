/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranscendentalAcyclicTranslation
public import FLT.Mazur.OriginalFiniteCoefficientOrbit
public import FLT.Mazur.OrderedCurvePowerIntegral
public import FLT.Mazur.GeometricSimultaneousHilbertTranslation

/-!
# Ordered original translations for arbitrary larger-field classes

Geometric nonemptiness and integral ordered powers construct one original
étale translation of the unchanged arbitrary K-class. Every independent
K-lift satisfies acyclicity with the same degree. K may be transcendental
over the original residue field; an embedded algebraic closure controls
all lifts without descending the class or its actual acyclic open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {R k L K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [Field k] [Field L] [Field K] [Algebra k L] [Algebra L K] [Algebra k K]
  [IsScalarTower k L K] [IsAlgClosed L] [Algebra.IsAlgebraic k L] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : AmpleLineBundle B)
  (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]

include L

omit [IsAlgClosed K] in
/-- Keep a prescribed degree when replacing a geometric ordered translation by an original test. -/
theorem exists_transcendental_ordered_translation_of_acyclicity
    (j : SmoothTranslationIndex) (d : ℕ)
    (s : (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := K) t)))
    (v : coefficientTest (K := K) t ⟶ smoothTranslationTest f j)
    (hv : s * (relativeFppfSheaf f).obj.map v.op (smoothTranslationClass f hB.2.1 j) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t))) :
    ∃ (E : Over (Spec (.of R))) (r : E ⟶ smoothTranslationTest f j)
      (_z : coefficientTest (K := K) t ⟶ E), IsAffine E.left ∧ Etale E.hom ∧
      ∀ w : coefficientTest (K := K) t ⟶ E,
        s * (relativeFppfSheaf f).obj.map w.op
          ((relativeFppfSheaf f).obj.map r.op (smoothTranslationClass f hB.2.1 j)) ∈
            (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t)) := by
  let T := coefficientTest (K := K) t
  let V := smoothTranslationTest f j
  let c := smoothTranslationClass f hB.2.1 j
  let Y : Over (Spec (.of R)) := Over.mk (pullback.fst V.hom T.hom ≫ V.hom)
  let a : Y ⟶ V := Over.homMk (pullback.fst V.hom T.hom)
  let b : Y ⟶ T := Over.homMk (pullback.snd V.hom T.hom) pullback.condition.symm
  have H : IsPullback a.left b.left V.hom T.hom := IsPullback.of_hasPullback _ _
  let _ := SmoothOfRelativeDimension.smooth 1 f
  let _ : GeometricallyIntegral V.hom := base_geometricallyIntegral f j.2
  let C := (relativeFppfSheaf f).obj.map b.op s * (relativeFppfSheaf f).obj.map a.op c
  let w : T ⟶ Y := Over.homMk
    (pullback.lift v.left (𝟙 _) (by rw [Category.id_comp]; exact v.w)) (by
      change _ ≫ (pullback.fst V.hom T.hom ≫ V.hom) = T.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact v.w)
  have hwa : w ≫ a = v := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have hwb : w ≫ b = 𝟙 _ := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  have hw : (relativeFppfSheaf f).obj.map w.op C ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T) := by
    dsimp only [C]
    rw [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hwb,
      op_id, (relativeFppfSheaf f).obj.map_id]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hwa]
    exact hv
  obtain ⟨l, _, _⟩ := (unpointedAcyclicDegreeOpen_represents f Y C d w).mp hw
  have hn : (unpointedAcyclicDegreeOpen f Y C d : Set Y.left).Nonempty :=
    ⟨(unpointedAcyclicDegreeArrow f Y C d).left (l.left (default : Spec (.of K))),
      ⟨l.left (default : Spec (.of K)), rfl⟩⟩
  obtain ⟨E, r, z, hE, he, hall⟩ :=
    exists_transcendental_all_independent_acyclic_translation (L := L) f t d a b H c s hn
  exact ⟨E, r, z, hE, he, hall⟩

include hB in
/-- Construct an original ordered affine étale translation valid at all independent lifts. -/
theorem exists_transcendental_ordered_all_lift_translation
    (s : (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := K) t))) :
    ∃ (j : SmoothTranslationIndex) (d : ℕ) (E : Over (Spec (.of R)))
      (r : E ⟶ smoothTranslationTest f j) (_z : coefficientTest (K := K) t ⟶ E),
      IsAffine E.left ∧ Etale E.hom ∧
      ∀ w : coefficientTest (K := K) t ⟶ E,
        s * (relativeFppfSheaf f).obj.map w.op
          ((relativeFppfSheaf f).obj.map r.op (smoothTranslationClass f hB.2.1 j)) ∈
            (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t)) := by
  let T := coefficientTest (K := K) t
  obtain ⟨d, M, hM⟩ := exists_simultaneous_geometric_acyclic_degree f hB T.hom
    (fun _ : Unit ↦ s)
  obtain ⟨j, v₀, hv⟩ := exists_smoothTranslation_geometric_class f hB T.hom (M ())
  let v : T ⟶ smoothTranslationTest f j := v₀
  have hv' : s * (relativeFppfSheaf f).obj.map v.op
      (smoothTranslationClass f hB.2.1 j) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T) := by
    change (relativeFppfSheaf f).obj.map v.op (smoothTranslationClass f hB.2.1 j) = _ at hv
    rw [hv]
    exact hM ()
  obtain ⟨E, r, z, hE, he, hall⟩ :=
    exists_transcendental_ordered_translation_of_acyclicity (L := L) f hB t j d s v hv'
  exact ⟨j, d, E, r, z, hE, he, hall⟩

end FLT.Mazur.HilbertChart
