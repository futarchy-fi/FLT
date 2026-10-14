/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedComparisonTransport
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The original affine morphism on a principal isomorphism neighborhood

Bijectivity of the actual base-localized ring map gives an isomorphism of
the original restricted scheme morphism, including its inclusion square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteCartierComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A bijective principal localization makes the actual restricted affine map an isomorphism. -/
theorem affine_principal_isIso {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (r : Γ(Y, ⊤))
    (hb : let _ := f.appTop.hom.toAlgebra
      Function.Bijective (algebraMap (Localization.Away r)
        (Localization (Algebra.algebraMapSubmonoid Γ(X, ⊤) (.powers r))))) :
    IsIso (f ∣_ Y.basicOpen r) := by
  let _ := f.appTop.hom.toAlgebra
  let B := Y.basicOpen r
  let C := f ⁻¹ᵁ B
  have hC : C = X.basicOpen (f.appTop r) := by
    exact Scheme.preimage_basicOpen_top f r
  let _ : IsAffine B.toScheme := (isAffineOpen_top Y).basicOpen r
  let _ : IsAffine C.toScheme := by
    rw [hC]
    exact (isAffineOpen_top X).basicOpen (f.appTop r)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, ⊤) (.powers r))
      Γ(C.toScheme, ⊤) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    change IsLocalization.Away (f.appTop r) Γ(C.toScheme, ⊤)
    rw [hC]
    infer_instance
  have hg : Function.Bijective (f ∣_ B).appTop.hom := by
    apply localized_bijective_of_commuting_square (.powers r)
      Γ(B.toScheme, ⊤) Γ(C.toScheme, ⊤) (f ∣_ B).appTop.hom _ hb
    change ((B).ι.appTop ≫ (f ∣_ B).appTop).hom =
      (f.appTop ≫ (C).ι.appTop).hom
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, morphismRestrict_ι]
  let _ : IsIso (f ∣_ B).appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hg
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (f ∣_ B))).mpr inferInstance

end FLT.Mazur.FiniteCartierComparison
