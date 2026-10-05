/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OverPoints
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Extension of points across a valuation ring

A point of a proper scheme over the fraction field of a valuation ring extends
uniquely to a point over that ring. The equalities are in the over category,
so the specified map to the base is retained. In particular this applies to
DVRs, providing G1-D1 of `docs/MAZUR_D_SPLIT.md`.

Source: the valuative criterion, Stacks 0BX5; Mazur (1977), III §5, p. 159.
This local theorem does not yet glue extensions over the Dedekind base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

variable {S : Scheme.{u}} (X : Over S)
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Separatedness makes valuation-ring extensions of a fraction-field point unique. -/
theorem Points.valuation_precomp_injective [IsSeparated X.hom]
    (s : Spec (CommRingCat.of R) ⟶ S) :
    Function.Injective (fun x : Points X s =>
      Points.precomp (Spec.map (CommRingCat.ofHom (algebraMap R K))) x) := by
  intro x y h
  let sq : ValuativeCommSq X.hom :=
    { R := R
      K := K
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x.left
      i₂ := s
      commSq := ⟨by simp [Over.w x]⟩ }
  let lx : sq.commSq.LiftStruct := ⟨x.left, rfl, Over.w x⟩
  let ly : sq.commSq.LiftStruct :=
    ⟨y.left, congrArg (fun z => z.left) h.symm, Over.w y⟩
  let : Subsingleton sq.commSq.LiftStruct := IsSeparated.valuativeCriterion X.hom sq
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l (Subsingleton.elim lx ly))

/-- A fraction-field point of a proper scheme extends uniquely across a valuation ring. -/
theorem Points.existsUnique_valuation_extension [IsProper X.hom]
    (s : Spec (CommRingCat.of R) ⟶ S)
    (x : Points X (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s)) :
    ∃! y : Points X s,
      Points.precomp (Spec.map (CommRingCat.ofHom (algebraMap R K))) y = x := by
  let sq : ValuativeCommSq X.hom :=
    { R := R
      K := K
      i₁ := x.left
      i₂ := s
      commSq := ⟨Over.w x⟩ }
  have hc : ValuativeCriterion X.hom := by
    have hp : IsProper X.hom := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  obtain ⟨l, hl, hs⟩ := (hc.existence sq).exists_lift
  refine ⟨Over.homMk l hs, Over.OverMorphism.ext hl, ?_⟩
  intro y hy
  apply Points.valuation_precomp_injective X (K := K) s
  exact hy.trans (Over.OverMorphism.ext hl).symm

/-- The DVR form of the point-extension theorem. -/
theorem Points.existsUnique_dvr_extension {A L : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field L] [Algebra A L] [IsFractionRing A L] [IsProper X.hom]
    (s : Spec (CommRingCat.of A) ⟶ S)
    (x : Points X (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ s)) :
    ∃! y : Points X s,
      Points.precomp (Spec.map (CommRingCat.ofHom (algebraMap A L))) y = x :=
  Points.existsUnique_valuation_extension X s x

end FLT.Mazur
