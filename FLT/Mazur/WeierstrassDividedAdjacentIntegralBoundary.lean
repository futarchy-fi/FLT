/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedBoundaryNormalization
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra

/-!
# Adjacent retained charts share their actual integral boundary

The common boundary equality comes from the defining exterior pushout.
It holds in the first whole model containing both charts and retains the
two original localization transitions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "F" => Exterior.advance hπ (E) e
local notation "G" => Exterior.advance hπ (F) fData
local notation "i" => olderSuccessiveChart hπ data j hj 1 hjNext
local notation "l" => olderSuccessiveChart hπ data (j + 1) hjNext 0 hjNext

/-- Both adjacent original charts agree on their shared boundary in the first common whole. -/
@[reassoc] theorem adjacentIntegral_boundary :
    nextToX e ≫ i = previousToX hπ e fData ≫ l := by
  change nextToX e ≫ (E).newX hπ e ≫
    (𝟙 _ ≫ (F).retained hπ fData) ≫ (G).exteriorChart =
      previousToX hπ e fData ≫ (F).newX hπ fData ≫ 𝟙 _ ≫ (G).exteriorChart
  simp only [Category.id_comp]
  have H := pushout.condition_assoc (f := (F).attach)
    (g := previousToX hπ e fData) (G).exteriorChart
  change (nextToX e ≫ (E).newX hπ e) ≫ _ ≫ _ = _ at H
  simpa only [Category.assoc, Exterior.newX, Exterior.retained] using H

open WeierstrassSuccessiveX
local notation "a" => depthOverlapEquiv W π (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "b" => previousBoundaryEquiv hπ e fData
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2

omit [IsDomain R] in
/-- The inverse depth equivalence is the whole original next-boundary inclusion. -/
@[reassoc] theorem depthOverlap_inverse_inclusion {k : ℕ} (d : Data W π (k + 1)) :
    Spec.map (CommRingCat.ofHom
      (depthOverlapEquiv W π k d.b3 d.b4 d.b6).symm.toRingHom) ≫
        xOpenInclusion W (π ^ k) π d.b3 d.b4 d.b6 = nextToX d := by
  rw [← depthOverlap_nextToX d]
  exact (Scheme.Spec.mapIso
    (depthOverlapEquiv W π k d.b3 d.b4 d.b6).toRingEquiv.toCommRingCatIso.op).inv_hom_id_assoc _

/-- The inverse horizontal equivalence is the whole original preceding-boundary inclusion. -/
@[reassoc] theorem previousBoundary_inverse_inclusion {k : ℕ}
    (d : Data W π k) (eNext : Data W π (k + 1)) :
    Spec.map (CommRingCat.ofHom (previousBoundaryEquiv hπ d eNext).symm.toRingHom) ≫
      horizontalOpenInclusion W (π ^ k) π eNext.b3 eNext.b4 eNext.b6 = previousToX hπ d eNext := by
  rw [← previousBoundaryEquiv_previousToX hπ d eNext]
  exact (Scheme.Spec.mapIso
    (previousBoundaryEquiv hπ d eNext).toRingEquiv.toCommRingCatIso.op).inv_hom_id_assoc _

/-- The original localization maps agree in the common whole before any contraction. -/
@[reassoc] theorem adjacentIntegral_localizations :
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm a).toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t))) ≫ i =
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm b).toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away u))) ≫ l := by
  change Spec.map _ ≫ xOpenInclusion _ _ _ _ _ _ ≫ i =
    Spec.map _ ≫ horizontalOpenInclusion _ _ _ _ _ _ ≫ l
  exact (depthOverlap_inverse_inclusion_assoc e i).trans
    ((adjacentIntegral_boundary hπ data j hj hjNext).trans
      (previousBoundary_inverse_inclusion_assoc hπ e fData l).symm)

end FLT.Mazur.WeierstrassDividedDepth
