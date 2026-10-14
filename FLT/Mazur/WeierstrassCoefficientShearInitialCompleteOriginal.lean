/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialCompleteNormalization
public import FLT.Mazur.WeierstrassCoefficientShearOriginalInitialConic
public import FLT.Mazur.WeierstrassDividedInitialExteriorOriented

/-!
# Reconstruction of the independent complete initial exterior

At root zero the independently extended incidence line is the entire original
projective exterior. The comparison retains the ordered normalization coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassModificationX

/-- Equal tangent coefficients preserve the whole incidence line. -/
@[reassoc] theorem fiberIncidenceImmersion_coefficientTransport
    {K : Type*} [CommRing K] {a b : K} (c : K) (h : a = b) :
    fiberIncidenceImmersion b c ≫
        Spec.map (CommRingCat.ofHom (fiberCoefficientTransport c h).toAlgHom.toRingHom) =
      fiberIncidenceImmersion a c := by
  subst b
  simp [fiberCoefficientTransport]

end FLT.Mazur.WeierstrassModificationX
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth) (hdepth : 0 < depth)
local notation "K" => ResidueField R
variable (hs : algebraMap R (ResidueField R) (π ^ start) = 0)
  (h3 : algebraMap R (ResidueField R) (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R (ResidueField R) (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "E" => coefficientShearGluedIso hπ data K 0 j hj
local notation "p" => coefficientShearGluedStructure hπ data K 0 j hj
local notation "N" => coefficientShearInitialCompleteNormalization hπ data K 0 j hj hs h3 h4 hr
local notation "f" => initialProjectiveToGlobal hπ data D j hj hstart hk hdepth

/-- Reconstruction identifies the full root-zero incidence line with its original immersion. -/
@[reassoc] theorem coefficientShearInitialLine_original :
    coefficientShearInitialLine hπ data K 0 j hj hs h3 h4 hr ≫ (E).hom =
      initialGlobalIncidenceLine hπ data D j hj hstart hk := by
  rw [coefficientShearInitialLine, Category.assoc,
    coefficientShearInitialFiber_original hπ data D j hj hstart hk hs h3 h4 hr]
  exact fiberIncidenceImmersion_coefficientTransport_assoc
    (residue R (data ⟨0, Nat.zero_lt_succ n⟩).b6)
    (rootShearZero_tangent (W.map (residue R))).symm
    (initialGlobalResidueFiberChart hπ data D j hj hstart hk)

/-- The independent proper extension is the full original projective exterior at root zero. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_original : N ≫ (E).hom = f := by
  have H : f ≫ (E).inv = N := by
    apply coefficientShearInitialCompleteNormalization_unique
    · simp only [coefficientShearGluedStructure, Category.assoc, Iso.inv_hom_id_assoc]
      rw [initialProjectiveToGlobal, Category.assoc, ← initialExteriorStructure,
        ← initialExteriorProjectiveIso_structure hπ data D j hj hstart hk hdepth,
        Iso.inv_hom_id_assoc]
    · rw [initialProjectiveToGlobal_affine_assoc,
        ← coefficientShearInitialLine_original hπ data D j hj hstart hk hs h3 h4 hr,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← H, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The ordered independent exterior reconstructs the complete original ordered component. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_ordered_original :
    (slopeNormalizationIso (WeierstrassDilatation.residueTangentUnit D)).inv ≫
        N ≫ (E).hom = initialOrientedToGlobal hπ data D j hj hstart hk hdepth := by
  have hu : WeierstrassDilatation.residueTangentUnit D =
      Units.mk0 (residue R W.a₁) (IsUnit.ne_zero (residue_tangent_isUnit D)) := by
    apply Units.ext
    exact WeierstrassDilatation.residueTangentUnit_val D
  rw [coefficientShearInitialCompleteNormalization_original, initialOrientedToGlobal_eq, hu]

end FLT.Mazur.WeierstrassDividedDepth
