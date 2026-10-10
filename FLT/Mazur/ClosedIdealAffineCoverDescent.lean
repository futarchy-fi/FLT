/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealSheafCoverComparison
public import FLT.Mazur.ClosedIdealCoverGluing

/-!
# Effective descent of actual ideal sheaves on affine open covers

Compatible full ideal sheaves on an affine open cover glue to a unique ideal
sheaf. The inverse is the kernel of the constructed glued closed immersion;
no descent conclusion is part of the input data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (C : X.OpenCover.{u})

/-- Actual local ideal sheaves with the equality required on their pairwise intersections. -/
def CompatibleIdeals :=
  { J : ∀ i : C.I₀, (C.X i).IdealSheafData //
    ∀ i j, (J i).comap (pullback.fst (C.f i) (C.f j)) =
      (J j).comap (pullback.snd (C.f i) (C.f j)) }

/-- Restriction of a global ideal supplies compatible full ideals on the cover. -/
def restrictIdeal (J : X.IdealSheafData) : CompatibleIdeals C :=
  ⟨fun i ↦ J.comap (C.f i), fun i j ↦ by
    rw [← comap_comp, ← comap_comp, pullback.condition]⟩

/-- Glue the actual closed families and take the kernel of the resulting closed immersion. -/
def descendIdeal (J : CompatibleIdeals C) : X.IdealSheafData :=
  (toBase C J.val J.property).ker

/-- The descended ideal restricts to each supplied ideal with its full scheme structure. -/
theorem descendIdeal_restrict (J : CompatibleIdeals C) (i : C.I₀) :
    (descendIdeal C J).comap (C.f i) = J.val i :=
  ker_toBase_comap C J.val J.property i

/-- Restriction after actual descent recovers all the compatible input ideals. -/
theorem restrictIdeal_descendIdeal (J : CompatibleIdeals C) :
    restrictIdeal C (descendIdeal C J) = J := by
  apply Subtype.ext
  funext i
  exact descendIdeal_restrict C J i

variable [∀ i, IsAffine (C.X i)]

/-- A global ideal is recovered by actual descent of its restrictions to the affine cover. -/
theorem descendIdeal_restrictIdeal (J : X.IdealSheafData) :
    descendIdeal C (restrictIdeal C J) = J := by
  apply BaseAdicThickening.idealSheaf_ext_of_affineCover C
  intro i
  exact descendIdeal_restrict C (restrictIdeal C J) i

/-- Compatible ideals have a unique effective descent on an affine open cover. -/
theorem descendIdeal_unique (J : CompatibleIdeals C) (K : X.IdealSheafData)
    (hK : ∀ i, K.comap (C.f i) = J.val i) : K = descendIdeal C J := by
  apply BaseAdicThickening.idealSheaf_ext_of_affineCover C
  intro i
  exact (hK i).trans (descendIdeal_restrict C J i).symm

/-- Effective descent equivalence for full ideal sheaves on an affine open cover. -/
def idealDescentEquiv : X.IdealSheafData ≃ CompatibleIdeals C where
  toFun := restrictIdeal C
  invFun := descendIdeal C
  left_inv := descendIdeal_restrictIdeal C
  right_inv := restrictIdeal_descendIdeal C

end FLT.Mazur.ClosedIdealCover
