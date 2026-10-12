/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceResidueShearComparison
public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassDividedInitialConicParameters

/-!
# The complete sheared initial conic reconstructs the original initial conic

Both full parameter opens agree with their original maps after reconstruction.
The proof compares the entire tensor equation before passing to the conic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R (Data.b6 d)
variable (hs : algebraMap R (ResidueField R) (π ^ start) = 0)
  (h3 : algebraMap R (ResidueField R) (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R (ResidueField R) (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "H" => fiberCoefficientTransport c (Eq.symm (rootShearZero_tangent V))
local notation "C" => conicCoefficientTransport c (Eq.symm (rootShearZero_tangent V))
local notation "E" => coefficientShearGluedIso hπ data K 0 j hj
local notation "fiber" => coefficientShearInitialFiber hπ data K 0 j hj hs h3 h4 hr
local notation "conic" => coefficientShearInitialConic hπ data K 0 j hj hs h3 h4 hr

/-- Reconstruction identifies the whole sheared incidence fiber with its original tensor map. -/
@[reassoc] theorem coefficientShearInitialFiber_original :
    fiber ≫ (E).hom = Spec.map (CommRingCat.ofHom (H).toAlgHom.toRingHom) ≫
      initialGlobalResidueFiberChart hπ data D j hj hstart hk := by
  rw [coefficientShearInitialFiber_reconstruction, globalInitialCoefficientShearChart,
    initialGlobalResidueFiberChart, ← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ globalInitialTensorChart hπ data K j hj)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom f).toRingHom))
    (residueFiberEquiv_eq_shear D hstart hk d hs h3 h4 hr).symm

/-- The complete exceptional conic reconstructs its original parameterized immersion. -/
@[reassoc] theorem coefficientShearInitialConic_original :
    conic ≫ (E).hom = Spec.map (CommRingCat.ofHom (C).toAlgHom.toRingHom) ≫
      initialGlobalConic hπ data D j hj hstart hk := by
  rw [coefficientShearInitialConic, Category.assoc,
    coefficientShearInitialFiber_original hπ data D j hj hstart hk hs h3 h4 hr]
  exact fiberConicImmersion_coefficientTransport_assoc c _
    (initialGlobalResidueFiberChart hπ data D j hj hstart hk)

variable (hu : IsUnit (rootShearCurve (W.map (residue R)) 0).a₁)

/-- The full first coefficient conic parameter retains the original affine origin. -/
@[reassoc] theorem coefficientShearInitialFirstParameter_original :
    coefficientConicFirstParameter (U).a₁ c hu conic ≫ (E).hom =
      initialGlobalConicFirstParameter hπ data D j hj hstart hk := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearInitialConic_original hπ data D j hj hstart hk hs h3 h4 hr,
    conicFirstParameter_coefficientTransport_assoc c _ (residue_tangent_isUnit D) hu]
  rfl

/-- The full opposite parameter preserves the original ordered second conic origin. -/
@[reassoc] theorem coefficientShearInitialSecondParameter_original :
    coefficientConicSecondParameter (U).a₁ c hu conic ≫ (E).hom =
      initialGlobalConicSecondParameter hπ data D j hj hstart hk := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearInitialConic_original hπ data D j hj hstart hk hs h3 h4 hr,
    conicSecondParameter_coefficientTransport_assoc c _ (residue_tangent_isUnit D) hu]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
