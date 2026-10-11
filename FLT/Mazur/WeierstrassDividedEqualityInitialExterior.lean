/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExteriorOriented
public import FLT.Mazur.WeierstrassDividedEqualityNodeFamily

/-!
# The original positive-start exterior in the equality-depth family

The complete exterior keeps its original affine incidence and infinity charts.
Its oriented endpoints are the two initial nodes in the fixed final model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- The full original oriented exterior as a component over the residue field. -/
def equalityInitialExteriorOverComponent : PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (initialOrientedToGlobal hπ data D (s + 1) hs hstart (by omega) (by omega))
    (initialOrientedToGlobal_structure hπ data D (s + 1) hs hstart (by omega) (by omega))

/-- Zero is precisely the first original initial section. -/
@[reassoc] theorem equalityInitialExteriorOverComponent_zero :
    ProjectiveLine.zeroSection K ≫
        equalityInitialExteriorOverComponent hπ data D s hs hstart hk =
      equalityNodeOverSection hπ data D s hs hk (.inl ⟨0, hstart⟩) := by
  apply Over.OverMorphism.ext
  exact initialOrientedToGlobal_zero hπ data D (s + 1) hs hstart (by omega) (by omega)

/-- Infinity is precisely the second original initial section. -/
@[reassoc] theorem equalityInitialExteriorOverComponent_infinity :
    ProjectiveLine.infinitySection K ≫
        equalityInitialExteriorOverComponent hπ data D s hs hstart hk =
      equalityNodeOverSection hπ data D s hs hk (.inl ⟨1, hstart⟩) := by
  apply Over.OverMorphism.ext
  exact initialOrientedToGlobal_infinity hπ data D (s + 1) hs hstart (by omega) (by omega)

/-- The component map recovers the complete original exterior, not just its markings. -/
@[reassoc] theorem equalityInitialExteriorOverComponent_original :
    (initialExteriorOrientedIso hπ data D (s + 1) hs hstart (by omega) (by omega)).hom ≫
        (equalityInitialExteriorOverComponent hπ data D s hs hstart hk).left =
      initialExteriorToGlobal hπ data D (s + 1) hs hstart (by omega) := by
  change _ ≫ initialOrientedToGlobal hπ data D (s + 1) hs hstart _ _ = _
  rw [initialOrientedToGlobal, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
