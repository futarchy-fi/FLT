/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearComponents
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleComponents
public import FLT.Mazur.WeierstrassConicCoefficientTransport

/-!
# Original residue lines agree with the root-zero sheared lines

Compare the entire tensor algebra restrictions on the original three generators.
This includes the affine origin and does not require cancelling the line parameter.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (D : SplitNodeDepth W π depth) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ depth)
  (d : Data W π (k + 1))
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R d.b6
variable (hs : algebraMap R (ResidueField R) (π ^ k) = 0)
  (hp : algebraMap R (ResidueField R) π = 0)
  (h3 : algebraMap R (ResidueField R) d.b3 = 0)
  (h4 : algebraMap R (ResidueField R) d.b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
  (v : ResidueField R) (hv : v * (v + residue R W.a₁) = 0)
  (hu : v * (v + (rootShearCurve (W.map (residue R)) 0).a₁) = 0)
local notation "E" => residueRetainedFiberEquiv D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "F" => tensorShearLineMap W (π ^ k) π d.b3 d.b4 d.b6 K 0 hs hp h3 h4 hr v hu

/-- Root-zero shearing preserves the full original residue line restriction. -/
theorem residueSuccessiveLineMap_eq_shear :
    (middleLineMap V c ((residue_eq_zero_iff _).mpr D.a₂_mem) v hv).comp
      (E).toAlgHom = F := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change middleLineMap V c ((residue_eq_zero_iff _).mpr D.a₂_mem) v hv
      (E (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)) =
    F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)
  rw [residueRetainedFiberEquiv_coord, middleLineMap_coord, tensorShearLineMap_coord]
  simp only [add_zero]

/-- The whole original line immersion equals its independently constructed sheared immersion. -/
theorem residueSuccessiveLineImmersion_eq_shear :
    residueSuccessiveLineImmersion D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4 v hv =
      Spec.map (CommRingCat.ofHom (F).toRingHom) := by
  unfold residueSuccessiveLineImmersion middleLineImmersion residueRetainedIso
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (residueSuccessiveLineMap_eq_shear D hk0 hk d hs hp h3 h4 hr v hv hu)

end FLT.Mazur.WeierstrassSuccessiveX
