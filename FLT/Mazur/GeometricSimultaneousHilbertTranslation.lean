/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricHilbertTranslation
public import FLT.Mazur.GeometricPicardSheafRepresentative
public import FLT.Mazur.VariableHilbertAcyclicLiftCriterion

/-!
# Simultaneous fixed-degree acyclic translations on the original geometric test

Construct a single actual acyclic Hilbert parameter, then represent the
required translations by actual lines. Every supplied original sheaf class
translates to this same divisor, so its degree is independent of the index.
The translations are constructed separately; they need not be restrictions
of one previously fixed translation class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))

/-- Arbitrary original geometric classes have actual line translations to one fixed divisor. -/
theorem exists_simultaneous_geometric_hilbert_translation {ι : Type}
    (s : ι → (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (a : Over.mk t ⟶ acyclicHilbertTest f d)
      (M : ι → LineBundle (pullback f t)), ∀ i,
      s i * relativeFppfClass f (Over.mk t) (relativeClass _ (mk (M i).val (M i).property)) =
        acyclicHilbertPicardPoint f d hL _ a := by
  obtain ⟨d, a, _, _⟩ := exists_geometric_hilbert_translation f hL t 1
  let p : (relativeFppfSheaf f).obj.obj (op (Over.mk t)) :=
    acyclicHilbertPicardPoint f d hL (Over.mk t) a
  have h (i : ι) := exists_geometric_picardSheaf_line f t (p / s i)
  choose M hM using h
  refine ⟨d, a, M, fun i ↦ ?_⟩
  rw [hM i, ← mul_div_assoc, mul_comm (s i), mul_div_cancel_right]

include hL in
/-- All constructed translated classes belong to the same original acyclic degree subfunctor. -/
theorem exists_simultaneous_geometric_acyclic_degree {ι : Type}
    (s : ι → (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (M : ι → LineBundle (pullback f t)), ∀ i,
      s i * relativeFppfClass f (Over.mk t) (relativeClass _ (mk (M i).val (M i).property)) ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨d, a, M, hM⟩ := exists_simultaneous_geometric_hilbert_translation f hL t s
  refine ⟨d, M, fun i ↦ ?_⟩
  rw [hM i]
  exact ((acyclicHilbertPicardIso f d hL).hom.app (op (Over.mk t)) (ULift.up a)).property

end FLT.Mazur.HilbertChart
