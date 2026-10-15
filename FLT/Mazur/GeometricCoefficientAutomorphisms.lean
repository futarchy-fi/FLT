/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianFiberAutomorphismAction
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Semilinear coefficient automorphisms of geometric fibers

The complete coefficient automorphism group acts on the actual cartesian
fiber. This construction fixes the original scheme coordinate and records
the field-coordinate change, including its orientation under Spec.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GeometricCoefficientAutomorphisms
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- Coefficient automorphisms as actual automorphisms of the field spectrum. -/
def specAction : (K ≃ₐ[k] K) →* Aut (Spec (.of K)) where
  toFun σ := Scheme.Spec.mapIso σ.symm.toRingEquiv.toCommRingCatIso.op
  map_one' := by
    apply Aut.ext
    change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 _
    exact Spec.map_id _
  map_mul' σ τ := by
    apply Aut.ext
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1

@[reassoc (attr := simp)]
theorem specAction_base (σ : K ≃ₐ[k] K) :
    (specAction σ).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact σ.symm.toAlgHom.comp_algebraMap

variable {Y V : Scheme} {a : Y ⟶ V} {b : Y ⟶ Spec (.of K)}
  {f : V ⟶ Spec (.of k)}
  (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- The complete coefficient action on the specified original cartesian fiber. -/
def fiberAction : (K ≃ₐ[k] K) →* Aut Y :=
  CartesianFiberAutomorphismAction.action H specAction specAction_base

@[reassoc (attr := simp)]
theorem fiberAction_fst (σ : K ≃ₐ[k] K) : (fiberAction H σ).hom ≫ a = a :=
  CartesianFiberAutomorphismAction.action_fst H specAction specAction_base σ

@[reassoc (attr := simp)]
theorem fiberAction_snd (σ : K ≃ₐ[k] K) :
    (fiberAction H σ).hom ≫ b = b ≫ (specAction σ).hom :=
  CartesianFiberAutomorphismAction.action_snd H specAction specAction_base σ

/-- Correcting the coefficient coordinate gives a geometric morphism over the identity. -/
theorem normalized_conjugate_base (w : Spec (.of K) ⟶ Y) (hw : w ≫ b = 𝟙 _)
    (σ : K ≃ₐ[k] K) :
    (specAction σ).inv ≫ w ≫ (fiberAction H σ).hom ≫ b = 𝟙 _ := by
  rw [fiberAction_snd, ← Category.assoc w, hw, Category.id_comp, Iso.inv_hom_id]

/-- The normalized conjugate retains the whole conjugated original scheme morphism. -/
theorem normalized_conjugate_fst (w : Spec (.of K) ⟶ Y) (σ : K ≃ₐ[k] K) :
    (specAction σ).inv ≫ w ≫ (fiberAction H σ).hom ≫ a =
      (specAction σ).inv ≫ w ≫ a := by rw [fiberAction_fst]

end FLT.Mazur.GeometricCoefficientAutomorphisms
