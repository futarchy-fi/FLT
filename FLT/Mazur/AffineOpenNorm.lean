/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePreimageRestrictionPushout
public import FLT.Mazur.AffineRelationNorm

/-!
# Norms on actual affine target opens

A local basis belongs to the whole preimage of a target open. Restriction
transports that basis through the cartesian section algebra, and the resulting
norms agree even when the smaller open has a separately chosen basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineOpenNorm
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- Genuine finite freeness over the entire original preimage of an affine open. -/
def HasBasis (U : Y.affineOpens) : Prop :=
  let _ := (f ∣_ U.1).appTop.hom.toAlgebra
  ∃ n : ℕ, Nonempty (Basis (Fin n) Γ(U.1, ⊤) Γ((f ⁻¹ᵁ U.1).toScheme, ⊤))

/-- The local norm, returned in the original structure sheaf. -/
def norm (U : Y.affineOpens) (s : Γ(X, f ⁻¹ᵁ U.1)) : Γ(Y, U.1) :=
  U.1.topIso.hom (AffineRelationNorm.sectionNorm (f ∣_ U.1)
    ((f ⁻¹ᵁ U.1).topIso.inv s))

/-- Every smaller affine target open inherits a basis of its entire preimage. -/
theorem HasBasis.restrict {U V : Y.affineOpens} (hU : HasBasis f U) (h : V ≤ U) :
    HasBasis f V := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let _ := (f ∣_ U.1).appTop.hom.toAlgebra
  let _ := (f ∣_ V.1).appTop.hom.toAlgebra
  obtain ⟨n, ⟨b⟩⟩ := hU
  exact ⟨n, ⟨AffineCartesianNorm.sectionBasis _ _ _ _
    (AffinePreimageRestriction.isPullback f h) b⟩⟩

/-- Local norms commute with the actual restriction maps of the original schemes. -/
theorem norm_restrict {U V : Y.affineOpens} (hU : HasBasis f U) (h : V ≤ U)
    (s : Γ(X, f ⁻¹ᵁ U.1)) :
    Y.presheaf.map (homOfLE h).op (norm f U s) =
      norm f V (X.presheaf.map (homOfLE (f.preimage_mono h)).op s) := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let _ := (f ∣_ U.1).appTop.hom.toAlgebra
  obtain ⟨n, ⟨b⟩⟩ := hU
  unfold norm
  erw [Approximation.topIso_hom_restriction (X := Y) h,
    ← Approximation.topIso_inv_restriction (X := X) (f.preimage_mono h)]
  congr 1
  exact (AffineRelationNorm.sectionNorm_pullback
    (AffinePreimageRestriction.isPullback f h) b _).symm

omit [IsAffineHom f] in
/-- Multiplication is preserved on every genuine finite free chart. -/
theorem norm_mul (U : Y.affineOpens) (s t : Γ(X, f ⁻¹ᵁ U.1)) :
    norm f U (s * t) = norm f U s * norm f U t := by
  unfold norm AffineRelationNorm.sectionNorm
  simp only [map_mul]

omit [IsAffineHom f] in
/-- The local norm of one is one. -/
theorem norm_one (U : Y.affineOpens) : norm f U 1 = 1 := by
  unfold norm AffineRelationNorm.sectionNorm
  simp only [map_one]

end FLT.Mazur.AffineOpenNorm
