/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFunctionGroundChange

/-!
# Structural function diagrams of full scheme relations

A map of two-endpoint relations over an arbitrary scheme gives the original
map of invariant function algebras. Both endpoint squares are proved from
the geometric diagram, without replacing either relation by a quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationFunctionDiagram
open SchemeFunctionGroundChange FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{0}} {A D B E : Over S}
  (p q : D ⟶ A) (r s : E ⟶ B) (u : B ⟶ A) (v : E ⟶ D)
  (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)

attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

include hp in
/-- An actual endpoint square gives the original square on function algebras. -/
theorem endpoint_square : (sectionMap r).comp (sectionMap u) =
    (sectionMap v).comp (sectionMap p) := by
  ext a
  change r.left.appTop (u.left.appTop a) = v.left.appTop (p.left.appTop a)
  have h := congrArg (fun b ↦ b.left.appTop a) hp
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using h.symm

/-- The invariant function map induced by both original geometric endpoint squares. -/
def invariantMap : AlgHom.equalizer (sectionMap p) (sectionMap q) →ₐ[Γ(S, ⊤)]
    AlgHom.equalizer (sectionMap r) (sectionMap s) :=
  equalizerMap _ _ _ _ (sectionMap u) (sectionMap v)
    (endpoint_square p r u v hp) (endpoint_square q s u v hq)

/-- On source coefficients this is exactly the original geometric restriction. -/
theorem invariantMap_val (a : AlgHom.equalizer (sectionMap p) (sectionMap q)) :
    (invariantMap p q r s u v hp hq a).val = u.left.appTop a.val := rfl

variable (C : Type*) [CommRing C] [Algebra Γ(S, ⊤) C]

/-- Restriction on full tensor equations, with all geometric endpoints retained. -/
def tensorInvariantMap :
    AlgHom.equalizer (tensorMap C (sectionMap p)) (tensorMap C (sectionMap q)) →ₐ[C]
      AlgHom.equalizer (tensorMap C (sectionMap r)) (tensorMap C (sectionMap s)) :=
  tensorEqualizerMap _ _ _ _ (sectionMap u) (sectionMap v)
    (endpoint_square p r u v hp) (endpoint_square q s u v hq) C

/-- The full tensor invariant restriction uses the actual source tensor map. -/
theorem tensorInvariantMap_val
    (a : AlgHom.equalizer (tensorMap C (sectionMap p)) (tensorMap C (sectionMap q))) :
    (tensorInvariantMap p q r s u v hp hq C a).val = tensorMap C (sectionMap u) a.val := rfl

end FLT.Mazur.SchemeRelationFunctionDiagram
