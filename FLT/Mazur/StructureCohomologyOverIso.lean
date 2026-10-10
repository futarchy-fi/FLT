/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleOpenCohomologyRestriction

/-!
# Structure cohomology through an isomorphism over a field

Scheme-isomorphism transport and the actual restriction of the unit module
identify structure cohomology, with linearity for the specified structure maps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] {X Y : Scheme}

/-- Module cohomology transport retains the field action from the structure morphism. -/
def moduleScalarHRestrictIsoEquiv (e : X ≅ Y) (f : Y ⟶ Spec (.of K))
    (M : Y.Modules) (n : ℕ) :
    ModuleScalarH f M n ≃ₗ[K] ModuleScalarH (e.hom ≫ f) (M.restrict e.hom) n := by
  refine { toAddEquiv := moduleHIsoEquiv e M n, map_smul' := ?_ }
  intro r x
  change ModuleH M n at x
  have hs : structureScalarMap (e.hom ≫ f) r = e.hom.appTop (structureScalarMap f r) := by
    simp [structureScalarMap]
  change moduleHIsoEquiv e M n (structureScalarMap f r • x) =
    structureScalarMap (e.hom ≫ f) r • moduleHIsoEquiv e M n x
  rw [moduleHIsoEquiv_smul, hs]

/-- Structure cohomology is invariant under an actual scheme isomorphism over the base. -/
def structureScalarHIsoEquiv (e : X ≅ Y) (f : Y ⟶ Spec (.of K)) (n : ℕ) :
    ScalarH f n ≃ₗ[K] ScalarH (e.hom ≫ f) n :=
  (moduleScalarHUnitEquiv f n).symm.trans
    ((moduleScalarHRestrictIsoEquiv e f (structureUnitModule Y) n).trans
      ((((moduleScalarHFunctor (e.hom ≫ f) n).mapIso
        (Scheme.Modules.restrictUnitIso e.hom)).toLinearEquiv).trans
        (moduleScalarHUnitEquiv (e.hom ≫ f) n)))

/-- Specified equal structure maps transport cohomology without changing the field action. -/
def structureScalarHOverIsoEquiv (e : X ≅ Y) (f : Y ⟶ Spec (.of K))
    (g : X ⟶ Spec (.of K)) (h : e.hom ≫ f = g) (n : ℕ) :
    ScalarH f n ≃ₗ[K] ScalarH g n :=
  h ▸ structureScalarHIsoEquiv e f n

/-- An isomorphism over the field preserves the dimension of actual structure cohomology. -/
theorem structureScalarH_finrank_of_overIso (e : X ≅ Y) (f : Y ⟶ Spec (.of K))
    (g : X ⟶ Spec (.of K)) (h : e.hom ≫ f = g) (n : ℕ) :
    Module.finrank K (ScalarH f n) = Module.finrank K (ScalarH g n) :=
  (structureScalarHOverIsoEquiv e f g h n).finrank_eq

end FLT.Mazur.FCurve
