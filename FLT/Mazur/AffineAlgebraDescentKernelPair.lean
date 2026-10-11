/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentScheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The original affine overlap is the effective scheme kernel pair

The two maps from the tensor overlap retain the specified coaction and the
original coefficient inclusion. They are the kernel pair of the constructed
affine scheme projection. Faithful flatness makes its cofork a scheme colimit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B)

/-- The original first endpoint is the spectrum of the supplied coaction. -/
def overlapFst : Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom D.coaction.toRingHom)

/-- The original second endpoint retains the coefficient factor. -/
def overlapSnd : Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- Both original overlap endpoints have the same constructed quotient image. -/
theorem overlap_condition :
    overlapFst D ≫ schemeProjection D = overlapSnd (R := R) (S := S) (B := B) ≫
      schemeProjection D := by
  rw [overlapFst, overlapSnd, schemeProjection, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun b ↦ (mem_invariants D b.val).mp b.property)

/-- The unchanged overlap is the actual scheme kernel pair of the constructed projection. -/
theorem overlap_isPullback [Module.Flat R S] :
    IsPullback (overlapFst D) (overlapSnd (R := R) (S := S) (B := B))
      (schemeProjection D) (schemeProjection D) := by
  apply IsPullback.of_right _ (overlap_condition D) (scheme_isPullback D).flip
  have htop : overlapFst D ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [overlapFst, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext D.coaction.commutes
  have hbot : schemeProjection D ≫ schemeBase D =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [schemeProjection, schemeBase, ← Spec.map_comp]
    rfl
  rw [htop, hbot]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R S B)

/-- The constructed quotient is effective for arbitrary scheme targets. -/
def schemeCoforkIsColimit [Module.FaithfullyFlat R S] :
    IsColimit (Cofork.ofπ (schemeProjection D) (overlap_condition D)) := by
  let _ : QuasiCompact (schemeProjection D) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (invariants D).val.toRingHom)))
  exact isColimitCoforkOfEffectiveEpi (schemeProjection D) _ (overlap_isPullback D).isLimit

end FLT.Mazur.AffineAlgebraDescent
