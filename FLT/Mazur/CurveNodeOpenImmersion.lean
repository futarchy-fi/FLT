/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNode
public import FLT.Mazur.AdicCompletionAlgEquiv
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
/-!
# Nodes and open charts

The stalk map of an open immersion respects the scalar maps induced by the
structure morphisms. Its completed algebra isomorphism transports IsNode.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.CurveNodeOpenImmersion
open FCurve.CurveNode
variable {K : Type u} [Field K] {U X : Scheme.{u}}
variable (j : U ⟶ X) (f : X ⟶ Spec (.of K)) (x : U)
theorem scalar_stalk (a : K) :
    (j.stalkMap x).hom (scalarMap f (j x) a) = scalarMap (j ≫ f) x a := by
  change j.stalkMap x (X.presheaf.germ ⊤ (j x) (by trivial)
    (f.appTop ((Scheme.ΓSpecIso (.of K)).inv a))) =
    U.presheaf.germ ⊤ x (by trivial) ((j ≫ f).appTop ((Scheme.ΓSpecIso (.of K)).inv a))
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.comp_appTop]
  rfl
/-- The actual stalk map with the structure-morphism scalar actions. -/
def stalkHom :
    letI := localAlgebra f (j x)
    letI := localAlgebra (j ≫ f) x
    LocalRing (j x) →ₐ[K] LocalRing x :=
  letI := localAlgebra f (j x)
  letI := localAlgebra (j ≫ f) x
  { (j.stalkMap x).hom with commutes' := scalar_stalk j f x }
/-- An open immersion induces an algebra isomorphism on actual stalks. -/
def stalkEquiv [IsOpenImmersion j] :
    letI := localAlgebra f (j x)
    letI := localAlgebra (j ≫ f) x
    LocalRing (j x) ≃ₐ[K] LocalRing x :=
  letI := localAlgebra f (j x)
  letI := localAlgebra (j ≫ f) x
  AlgEquiv.ofBijective (stalkHom j f x) (ConcreteCategory.bijective_of_isIso (j.stalkMap x))
/-- The induced algebra isomorphism on completed local rings. -/
def completedStalkEquiv [IsOpenImmersion j] :
    letI := localAlgebra f (j x)
    letI := localAlgebra (j ≫ f) x
    CompletedLocalRing (j x) ≃ₐ[K] CompletedLocalRing x :=
  letI := localAlgebra f (j x)
  letI := localAlgebra (j ≫ f) x
  AdicCompletionAlgEquiv.localEquivalence (stalkEquiv j f x)
theorem isNode_iff [IsOpenImmersion j] : IsNode f (j x) ↔ IsNode (j ≫ f) x := by
  let := localAlgebra f (j x)
  let := localAlgebra (j ≫ f) x
  constructor
  · rintro ⟨e⟩
    exact ⟨(completedStalkEquiv j f x).symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨(completedStalkEquiv j f x).trans e⟩
end FLT.Mazur.CurveNodeOpenImmersion
