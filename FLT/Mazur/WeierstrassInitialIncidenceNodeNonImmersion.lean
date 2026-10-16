/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInitialIncidenceNonImmersion
public import FLT.Mazur.WeierstrassModificationXIncidenceNodeRestriction

/-!
# Failure of the exact incidence normalization on the full smoothing node

Transport the explicit collision through the established full initial-node
isomorphism. Even with zero arithmetic ideal and unit a₁, the proposed pair
(t, q times the opposite factor) is not an open immersion of the full node.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.InitialIncidenceCollision
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
local notation "L" => PolynomialNodeOpen curve 0
local notation "O" => PolynomialInitialOpen curve 0 0 0 0 (0 : ℚ[X])
/-- The arithmetic ideal in the counterexample is zero, hence nilpotent. -/
theorem zeroIdeal_nilpotent : IsNilpotent (⊥ : Ideal ℚ) := ⟨1, by simp⟩
local notation "hI" => zeroIdeal_nilpotent

/-- The zero polynomial is an actual root of this original nodal conic. -/
theorem zeroRootEquation : (0 : ℚ[X]) ^ 2 + polynomialSlopeLinear curve 0 * 0 =
    polynomialSlopeConstant curve 0 0 := by
  simp [polynomialSlopeConstant, curve]

/-- The candidate incidence normalization on the entire node open D(q+1). -/
def nodeIncidenceMorphism : Spec (.of L) ⟶ PolygonSmoothing.chart ℚ 0 :=
  incidenceInitialMorphism curve 0 0 0 0 0 zeroRootEquation ⊥ hI (by simp) (by simp)

/-- The original source comparison is a genuine isomorphism, with no extra hypothesis. -/
def nodeSourceIso : Spec (.of L) ≅ Spec (.of O) :=
  polynomialNodeIso curve 0 0 0 0 0 zeroRootEquation ⊥ hI (by simp) (by simp)

/-- The proposed node normalization is the original incidence morphism under this isomorphism. -/
theorem nodeSourceIso_incidence :
    nodeSourceIso.hom ≫ openIncidenceMorphism = nodeIncidenceMorphism := by
  rw [openIncidenceMorphism_eq, ← Category.assoc]
  exact polynomialNodeChart_incidence curve 0 0 0 0 0 zeroRootEquation ⊥ hI
    (by simp) (by simp)

/-- The full-node form of the proposed normalization is not a monomorphism. -/
theorem nodeIncidenceMorphism_not_mono : ¬ Mono nodeIncidenceMorphism := by
  intro hm
  let _ := hm
  have hi : Mono (nodeSourceIso.inv ≫ nodeIncidenceMorphism) := inferInstance
  have he : nodeSourceIso.inv ≫ nodeIncidenceMorphism = openIncidenceMorphism := by
    rw [← nodeSourceIso_incidence, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [he] at hi
  exact openIncidenceMorphism_not_mono hi

/-- In particular, the full-chart extension suggested by the exact Laurent parameter fails. -/
theorem nodeIncidenceMorphism_not_isOpenImmersion :
    ¬ IsOpenImmersion nodeIncidenceMorphism := by
  intro h
  let _ := h
  exact nodeIncidenceMorphism_not_mono inferInstance

end FLT.Mazur.InitialIncidenceCollision
