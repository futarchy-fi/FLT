/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicThickening
public import FLT.Mazur.AffinePullbackIdeal

/-!
# Comparing actual ideal sheaves through affine tests

Extension of a coordinate ideal gives exactly the pullback ideal sheaf.
Equality can be checked on affine tests of an arbitrary scheme, retaining
nilpotents and the full ideal rather than only its support.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.BaseAdicThickening

set_option backward.isDefEq.respectTransparency false

/-- Extension of a coordinate ideal is the actual scheme pullback ideal. -/
theorem baseIdeal_comap_specMap {A B : CommRingCat.{u}} (J : Ideal A) (f : A ⟶ B) :
    (baseIdeal A J).comap (Spec.map f) = baseIdeal B (J.map f.hom) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [ideal_comap_top, baseIdeal_top, baseIdeal_top, Ideal.map_map, Ideal.map_map]
  apply congrArg (Ideal.map · J)
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality f).symm

/-- Equality of ideal sheaves is detected by their restrictions to all affine opens. -/
theorem idealSheaf_ext_of_affineRestrictions {X : Scheme.{u}} {J K : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, J.comap U.1.ι = K.comap U.1.ι) : J = K := by
  apply Scheme.IdealSheafData.ext
  funext U
  have he := congrArg (fun L : U.1.toScheme.IdealSheafData ↦
    L.ideal ⟨⊤, isAffineOpen_top U⟩) (h U)
  rw [ideal_comap_ι_top, ideal_comap_ι_top] at he
  apply_fun Ideal.map U.1.topIso.hom.hom at he
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id,
    CommRingCat.hom_id, Ideal.map_id] using he

/-- Arbitrary affine tests detect equality of ideal sheaves on any scheme. -/
theorem idealSheaf_ext_of_affineTests {X : Scheme.{u}} {J K : X.IdealSheafData}
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ X), J.comap f = K.comap f) : J = K := by
  apply idealSheaf_ext_of_affineRestrictions
  intro U
  have he := congrArg (fun L ↦ L.comap U.2.isoSpec.hom) (h Γ(X, U.1) U.2.fromSpec)
  simpa only [← comap_comp, U.2.isoSpec_hom_fromSpec] using he

end FLT.Mazur.BaseAdicThickening
