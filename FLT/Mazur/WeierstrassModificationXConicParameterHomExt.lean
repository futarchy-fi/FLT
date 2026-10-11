/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The two original conic parameters determine arbitrary target morphisms

The parameter opens form an actual scheme open cover. Equality on them
therefore detects equality of morphisms with arbitrary, possibly nonseparated, targets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
universe u
variable {R : Type u} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "p₁" => Iso.inv (conicFirstParameterIso a c ha) ≫ conicFirstOpenImmersion a c
local notation "p₂" => Iso.inv (conicSecondParameterIso a c ha) ≫ conicSecondOpenImmersion a c

/-- The two original ordered conic parameters detect equality into any target scheme. -/
theorem conicParameter_hom_ext {Y : Scheme.{u}}
    (f g : Spec (.of (ConicCoordinate a c)) ⟶ Y)
    (h₁ : p₁ ≫ f = p₁ ≫ g) (h₂ : p₂ ≫ f = p₂ ≫ g) : f = g := by
  let q : Fin 2 → (Spec (.of (ConicParameterOpen c)) ⟶
      Spec (.of (ConicCoordinate a c))) := Fin.cases p₁ (fun _ => p₂)
  have hq (i : Fin 2) : IsOpenImmersion (q i) := by
    fin_cases i
    · change IsOpenImmersion p₁
      infer_instance
    · change IsOpenImmersion p₂
      infer_instance
  let U : (Spec (.of (ConicCoordinate a c))).OpenCover := {
    I₀ := Fin 2
    X := fun _ => Spec (.of (ConicParameterOpen c))
    f := q
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, hq⟩
      intro x
      rcases conicOpenImmersions_cover a c ha x with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · refine ⟨0, (conicFirstParameterIso a c ha).hom z, ?_⟩
        change (((conicFirstParameterIso a c ha).hom ≫
          (conicFirstParameterIso a c ha).inv) ≫ conicFirstOpenImmersion a c) z = _
        simp only [Iso.hom_inv_id, Category.id_comp]
      · refine ⟨1, (conicSecondParameterIso a c ha).hom z, ?_⟩
        change (((conicSecondParameterIso a c ha).hom ≫
          (conicSecondParameterIso a c ha).inv) ≫ conicSecondOpenImmersion a c) z = _
        simp only [Iso.hom_inv_id, Category.id_comp] }
  apply U.hom_ext
  intro i
  fin_cases i
  · exact h₁
  · exact h₂

end FLT.Mazur.WeierstrassModificationX
