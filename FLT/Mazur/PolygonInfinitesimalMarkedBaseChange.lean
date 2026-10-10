/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalBaseChange
public import FLT.Mazur.PolygonInfinitesimalMarkings

/-!
# Markings under the actual infinitesimal family pullback

A coefficient unit and its image define compatible chart sections. The assembled
pullback comparison sends every global marking to the actual pulled-back section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (t : R)

/-- Evaluation at a unit commutes with the actual chart coefficient map. -/
theorem markedEvaluation_coefficient (a : Rˣ) :
    ((markedEvaluation (algebraMap R S t) (Units.map (algebraMap R S) a)).restrictScalars R).comp
      (coefficientAlgHom R S t) = (Algebra.ofId R S).comp (markedEvaluation t a) := by
  apply chartRing_hom_ext t <;> simp

/-- The local marked section square uses the specified unit image. -/
@[reassoc] theorem markedSection_coefficient (a : Rˣ) :
    markedSection (algebraMap R S t) (Units.map (algebraMap R S) a) ≫
      chartCoefficient R S t = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
        markedSection t a := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (markedEvaluation_coefficient R S t a))

variable [Fact (IsNilpotent t)] [Fact (IsNilpotent (algebraMap R S t))]
  (n : ℕ) (h : 2 ≤ n)

/-- The global coefficient projection preserves each specified unit marking. -/
@[reassoc] theorem marking_coefficientProjection (i : Fin n) (a : Rˣ) :
    marking S (algebraMap R S t) n h i (Units.map (algebraMap R S) a) ≫
      coefficientProjection R S t n h =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ marking R t n h i a := by
  rw [marking, Category.assoc, chart_coefficientProjection,
    ← Category.assoc, markedSection_coefficient, Category.assoc, marking]

/-- The family pullback comparison retains the entire marking, with both projections. -/
theorem marking_baseChangeIso (i : Fin n) (a : Rˣ) :
    marking S (algebraMap R S t) n h i (Units.map (algebraMap R S) a) ≫
      (baseChangeIso R S t n h).hom =
        pullback.lift
          (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ marking R t n h i a)
          (𝟙 _) (by rw [Category.assoc, marking_base, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeIso_fst, pullback.lift_fst,
      marking_coefficientProjection]
  · rw [Category.assoc, baseChangeIso_snd, pullback.lift_snd, marking_base]

end FLT.Mazur.PolygonInfinitesimal
