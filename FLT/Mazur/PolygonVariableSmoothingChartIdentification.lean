/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingRestriction
public import FLT.Mazur.PolygonSmoothingIdentificationGeometry

/-!
# Full chart inclusions with identified parameters

The equality of a node's parameter gives an explicit full-chart inclusion.
Both punctures and the coefficient projection keep that same identification.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonVariableSmoothing
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R)
  [∀ i, Fact (IsNilpotent (t i))] (h : 2 ≤ n)

/-- Include the entire chart using its proved parameter equality. -/
def chartWithParameter (i : Fin n) (a : R) (ha : a = t i) :
    PolygonSmoothing.chart R a ⟶ scheme R n t h :=
  (nodeParameterIso a (t i) ha).hom ≫ chart R n t h i

instance chartWithParameter_isOpenImmersion (i : Fin n) (a : R) (ha : a = t i) :
    IsOpenImmersion (chartWithParameter R n t h i a ha) := by
  unfold chartWithParameter
  infer_instance

/-- The full left puncture is unchanged by the parameter identification. -/
@[reassoc] theorem leftBranch_chartWithParameter (i : Fin n) (a : R) (ha : a = t i) :
    leftBranchOpen R a ≫ chartWithParameter R n t h i a ha =
      leftBranchOpen R (t i) ≫ chart R n t h i := by
  subst a
  simp only [chartWithParameter, nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]

/-- The incoming puncture retains its full inverse Laurent coordinate. -/
@[reassoc] theorem precedingBranch_chartWithParameter (i : Fin n) (a : R) (ha : a = t i) :
    precedingBranch R a ≫ chartWithParameter R n t h i a ha =
      precedingBranch R (t i) ≫ chart R n t h i := by
  subst a
  simp only [chartWithParameter, nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]

/-- Adjacent identified charts satisfy the exact cyclic gluing equation. -/
@[reassoc] theorem chartWithParameter_overlap
    (i k : Fin n) (hk : (finRotate n).symm i = k)
    (a b : R) (ha : a = t i) (hb : b = t k) :
    leftBranchOpen R a ≫ chartWithParameter R n t h i a ha =
      precedingBranch R b ≫ chartWithParameter R n t h k b hb := by
  rw [leftBranch_chartWithParameter, precedingBranch_chartWithParameter, overlap, hk]

variable {S : Type u} [CommRing S] (f : R →+* S) (s : Fin n → S)
  [∀ i, Fact (IsNilpotent (s i))] (hs : ∀ i, f (t i) = s i)

/-- Both whole-chart identifications commute with the actual coefficient map. -/
@[reassoc] theorem chartWithParameter_projection (i : Fin n)
    (a : R) (b : S) (ha : a = t i) (hb : b = s i) (hab : f a = b) :
    chartWithParameter S n s h i b hb ≫ parameterProjection f n t s hs h =
      Spec.map (CommRingCat.ofHom (ringMap f a b hab)) ≫
        chartWithParameter R n t h i a ha := by
  subst a
  subst b
  simp only [chartWithParameter, nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact chart_parameterProjection f n t s hs h i

end FLT.Mazur.PolygonVariableSmoothing
