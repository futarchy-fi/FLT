/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentRelativeRelation

/-!
# Compatible affine neighborhoods for original coaction relations

Every invariant open of the original coefficient spectrum has a basis of
principal affine opens defined by actual invariant coefficients. The two
unchanged overlap endpoints have the same inverse image of each neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B)

/-- Principal target opens pull back to principal opens of the original invariant coefficient. -/
theorem projection_preimage_basicOpen (r : invariants D) :
    schemeProjection D ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen r.val :=
  PrimeSpectrum.comap_basicOpen (invariants D).val.toRingHom r

/-- Both original overlap endpoints preserve the same invariant principal domain. -/
theorem invariant_basicOpen (r : invariants D) :
    overlapFst D ⁻¹ᵁ PrimeSpectrum.basicOpen r.val =
      overlapSnd (R := R) (S := S) (B := B) ⁻¹ᵁ PrimeSpectrum.basicOpen r.val := by
  rw [← projection_preimage_basicOpen D r, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, overlap_condition]

variable [Module.FaithfullyFlat R S]

/-- Saturation by the constructed projection preserves every original relation-invariant open. -/
theorem projection_saturation (W : (Spec (.of B)).Opens)
    (hW : overlapFst D ⁻¹ᵁ W = overlapSnd (R := R) (S := S) (B := B) ⁻¹ᵁ W) :
    schemeProjection D ⁻¹' (schemeProjection D '' (W : Set (Spec (.of B)))) = W := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha, hb⟩ := Scheme.exists_preimage_of_isPullback (overlap_isPullback D) y x he
    have hh := Set.ext_iff.mp (congrArg SetLike.coe hW) a
    change overlapFst D a ∈ W ↔ overlapSnd (R := R) (S := S) (B := B) a ∈ W at hh
    rw [ha, hb] at hh
    exact hh.mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Every original invariant open has an open image in the constructed invariant spectrum. -/
theorem projection_isOpen_image (W : (Spec (.of B)).Opens)
    (hW : overlapFst D ⁻¹ᵁ W = overlapSnd (R := R) (S := S) (B := B) ⁻¹ᵁ W) :
    IsOpen (schemeProjection D '' (W : Set (Spec (.of B)))) := by
  apply (Flat.isQuotientMap_of_surjective (schemeProjection D)).isOpen_preimage.mp
  rw [projection_saturation D W hW]
  exact W.isOpen

/-- Original invariant opens have affine principal refinements from the constructed fixed ring. -/
theorem exists_invariant_principal (W : (Spec (.of B)).Opens)
    (hW : overlapFst D ⁻¹ᵁ W = overlapSnd (R := R) (S := S) (B := B) ⁻¹ᵁ W)
    (x : Spec (.of B)) (hx : x ∈ W) :
    ∃ r : invariants D, x ∈ PrimeSpectrum.basicOpen r.val ∧
      PrimeSpectrum.basicOpen r.val ≤ W := by
  obtain ⟨V, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show schemeProjection D x ∈ schemeProjection D '' (W : Set (Spec (.of B))) from
        ⟨x, hx, rfl⟩) (projection_isOpen_image D W hW)
  refine ⟨r, ?_, ?_⟩
  · change x ∈ schemeProjection D ⁻¹ᵁ PrimeSpectrum.basicOpen r at hr
    rwa [projection_preimage_basicOpen] at hr
  · intro y hy
    have hh : y ∈ schemeProjection D ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
      rwa [projection_preimage_basicOpen]
    have hm := hsub hh
    change y ∈ schemeProjection D ⁻¹' (schemeProjection D '' (W : Set (Spec (.of B)))) at hm
    rwa [projection_saturation D W hW] at hm

omit [Module.FaithfullyFlat R S] in
/-- Each compatible neighborhood is affine in the unchanged coefficient scheme. -/
theorem invariant_principal_isAffine (r : invariants D) :
    IsAffineOpen (X := Spec (.of B)) (PrimeSpectrum.basicOpen r.val) :=
  IsAffineOpen.Spec_basicOpen (R := .of B) r.val

end FLT.Mazur.AffineAlgebraDescent
