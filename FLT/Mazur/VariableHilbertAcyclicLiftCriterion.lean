/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertAcyclicLift

/-!
# Exact geometric criterion for original Hilbert lifts

A class with a prescribed translation coordinate has an original Hilbert
lift exactly when its untranslated class has an actual acyclic divisor of
the fixed degree. The resulting map is unique on every scheme test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V)) {T : Over (Spec (.of R))}

/-- Every original chart map gives an actual acyclic divisor class after undoing translation. -/
theorem variableHilbertPoint_mul_translation_mem (a : T ⟶ variableHilbertTest f d V) :
    (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) *
      (relativeFppfSheaf f).obj.map (a ≫ variableHilbertBase f d V).op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op T) := by
  rw [variableChartSection_map, variableHilbertPoint, div_mul_cancel]
  exact ((acyclicHilbertPicardIso f d hL).hom.app (op T)
    (ULift.up (a ≫ variableHilbertParameter f d V))).property

/-- Acyclicity of fixed degree is exactly existence of a lift with the prescribed base and class. -/
theorem acyclicTranslation_mem_iff_exists
    (s : (relativeFppfSheaf f).obj.obj (op T)) (v : T ⟶ V) :
    s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T) ↔
    ∃ a : T ⟶ variableHilbertTest f d V, a ≫ variableHilbertBase f d V = v ∧
      (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) = s := by
  constructor
  · intro hs
    exact ⟨acyclicTranslationLift f hL d V c s v hs,
      acyclicTranslationLift_base f hL d V c s v hs,
      acyclicTranslationLift_class f hL d V c s v hs⟩
  · rintro ⟨a, hv, ha⟩
    have h := variableHilbertPoint_mul_translation_mem f hL d V c a
    rwa [hv, ha] at h

/-- The original chart lift is unique, on arbitrary nonreduced or nonaffine tests as well. -/
theorem acyclicTranslation_mem_iff_existsUnique
    (s : (relativeFppfSheaf f).obj.obj (op T)) (v : T ⟶ V) :
    s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T) ↔
    ∃! a : T ⟶ variableHilbertTest f d V, a ≫ variableHilbertBase f d V = v ∧
      (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) = s := by
  constructor
  · intro hs
    refine ⟨acyclicTranslationLift f hL d V c s v hs,
      ⟨acyclicTranslationLift_base f hL d V c s v hs,
        acyclicTranslationLift_class f hL d V c s v hs⟩, ?_⟩
    intro a ha
    exact acyclicTranslationLift_unique f hL d V c s v hs a ha.1 ha.2
  · intro h
    exact (acyclicTranslation_mem_iff_exists f hL d V c s v).mpr h.exists

end FLT.Mazur.HilbertChart
