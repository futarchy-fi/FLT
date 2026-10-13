/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineHomogeneousCoordinates
public import FLT.Mazur.ProjectiveLineCoefficientMap
public import FLT.Mazur.AffineSectionLineCoefficientMap

/-!
# The homogeneous and glued projective coefficient maps agree

Compare the two constructions on their entire affine charts, using universal
polynomial points. No endpoint-only determination of a projective map is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K L : Type u} [Field K] [Field L] (f : K →+* L)

/-- The homogeneous comparison preserves the actual coefficient map on the full line. -/
@[reassoc] theorem homogeneousIso_coefficientMap :
    (homogeneousIso L).hom ≫ ProjectiveSpace.coefficientMap f (ULift.{u} (Fin 2)) =
      coefficientMap f ≫ (homogeneousIso K).hom := by
  apply (cancel_mono (homogeneousIso K).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pushout.hom_ext
  · change left L ≫ _ = left L ≫ _
    have h := unitChartPoint_coefficientMap f (Polynomial.C : L →+* Polynomial L)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial L) i.down) (ULift.up 0) 1 rfl
    have hl := homogeneousPoint_left L (Polynomial.C : L →+* Polynomial L)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial L) i.down) 1 rfl
    have hk := homogeneousPoint_left K ((Polynomial.C : L →+* Polynomial L).comp f)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial L) i.down) 1 rfl
    have he : Polynomial.eval₂RingHom (Polynomial.C : L →+* Polynomial L) Polynomial.X =
        RingHom.id _ := by ext <;> simp
    have hf : Polynomial.eval₂RingHom ((Polynomial.C : L →+* Polynomial L).comp f)
        Polynomial.X = Polynomial.mapRingHom f := by ext <;> simp
    simp only [inv_one, Units.val_one, one_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, he, hf, CommRingCat.ofHom_id,
      Spec.map_id, Category.id_comp] at hl hk
    rw [left_coefficientMap, ← hl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h]
    exact hk
  · change right L ≫ _ = right L ≫ _
    have h := unitChartPoint_coefficientMap f (Polynomial.C : L →+* Polynomial L)
      (fun i => (![Polynomial.X, 1] : Fin 2 → Polynomial L) i.down) (ULift.up 1) 1 rfl
    have hl := homogeneousPoint_right L (Polynomial.C : L →+* Polynomial L)
      (fun i => (![Polynomial.X, 1] : Fin 2 → Polynomial L) i.down) 1 rfl
    have hk := homogeneousPoint_right K ((Polynomial.C : L →+* Polynomial L).comp f)
      (fun i => (![Polynomial.X, 1] : Fin 2 → Polynomial L) i.down) 1 rfl
    have he : Polynomial.eval₂RingHom (Polynomial.C : L →+* Polynomial L) Polynomial.X =
        RingHom.id _ := by ext <;> simp
    have hf : Polynomial.eval₂RingHom ((Polynomial.C : L →+* Polynomial L).comp f)
        Polynomial.X = Polynomial.mapRingHom f := by ext <;> simp
    simp only [inv_one, Units.val_one, one_mul, Matrix.cons_val_zero, he, hf, CommRingCat.ofHom_id,
      Spec.map_id, Category.id_comp] at hl hk
    rw [right_coefficientMap, ← hl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h]
    exact hk

end FLT.Mazur.ProjectiveLine
