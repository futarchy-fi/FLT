/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteGluing

/-!
# The initial finite global stage is the first whole modification

The local initial isomorphism identifies the full original Y-boundaries.
Gluing it with the identity at infinity gives a canonical comparison of the
entire initial stage with the existing global modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
open WeierstrassIntegralChart

/-- The initial local comparison identifies the exact original overlap embeddings. -/
@[reassoc] theorem finiteYBoundary_initialIso :
    finiteYBoundary hπ data 0 (Nat.zero_le n) ≫ (initialExteriorIso d₀).hom =
      WeierstrassGlobalModification.boundary W (π ^ start) (d₀).b3 (d₀).b4 (d₀).b6
        (d₀).factor3 (d₀).factor4 (d₀).factor6 (pow_ne_zero start hπ) := by
  let f := WeierstrassModificationX.affineContraction W (π ^ start)
    (d₀).b3 (d₀).b4 (d₀).b6 (d₀).factor3 (d₀).factor4 (d₀).factor6
  have H := WeierstrassModificationReesCoordinates.originalOpen_isPullback W (π ^ start)
    (d₀).b3 (d₀).b4 (d₀).b6 (d₀).factor3 (d₀).factor4 (d₀).factor6
    (pow_ne_zero start hπ) (coord W 2 1) (Ideal.subset_span (by simp))
  have h : IsIso (f ∣_ (overlapInclusion W 2 1).opensRange) :=
    SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _ H
  apply (SchemeUnchangedOpen.lift_unique f (overlapInclusion W 2 1) h _ ?_).trans
    (SchemeUnchangedOpen.lift_unique f (overlapInclusion W 2 1) h _
      (WeierstrassGlobalModification.boundary_contraction _ _ _ _ _ _ _ _ _)).symm
  have hc := finiteYBoundary_contraction hπ data 0 (Nat.zero_le n)
  change finiteYBoundary hπ data 0 (Nat.zero_le n) ≫
    (𝟙 _ ≫ ((initialExteriorIso d₀).hom ≫ f)) = _ at hc
  simpa only [Category.id_comp, Category.assoc] using hc

/-- Identify the entire initial finite global model with the first existing global model. -/
def finiteGlobalInitialIso : finiteGlobalModel hπ data 0 (Nat.zero_le n) ≅
    WeierstrassGlobalModification.model W (π ^ start) (d₀).b3 (d₀).b4 (d₀).b6
      (d₀).factor3 (d₀).factor4 (d₀).factor6 (pow_ne_zero start hπ) :=
  asIso (pushout.map _ _ _ _ (𝟙 _) (initialExteriorIso d₀).hom (𝟙 _)
    (by simp) (by simpa using finiteYBoundary_initialIso hπ data))

/-- The whole initial comparison is exactly the identity on the original infinity chart. -/
@[reassoc] theorem finiteGlobalInitialIso_infinity :
    finiteInfinityChart hπ data 0 (Nat.zero_le n) ≫ (finiteGlobalInitialIso hπ data).hom =
      WeierstrassGlobalModification.infinityChart W (π ^ start) (d₀).b3 (d₀).b4 (d₀).b6
        (d₀).factor3 (d₀).factor4 (d₀).factor6 (pow_ne_zero start hπ) := by
  simp [finiteGlobalInitialIso, finiteInfinityChart, WeierstrassGlobalModification.infinityChart]

/-- The whole initial comparison retains the actual initial local modification isomorphism. -/
@[reassoc] theorem finiteGlobalInitialIso_local :
    finiteLocalChart hπ data 0 (Nat.zero_le n) ≫ (finiteGlobalInitialIso hπ data).hom =
      (initialExteriorIso d₀).hom ≫
        WeierstrassGlobalModification.localChart W (π ^ start) (d₀).b3 (d₀).b4 (d₀).b6
          (d₀).factor3 (d₀).factor4 (d₀).factor6 (pow_ne_zero start hπ) := by
  simp [finiteGlobalInitialIso, finiteLocalChart, WeierstrassGlobalModification.localChart]

/-- The canonical initial whole comparison commutes with the actual original contraction. -/
@[reassoc] theorem finiteGlobalInitialIso_contraction :
    (finiteGlobalInitialIso hπ data).hom ≫
      WeierstrassGlobalModification.contraction W (π ^ start) (d₀).b3 (d₀).b4 (d₀).b6
        (d₀).factor3 (d₀).factor4 (d₀).factor6 (pow_ne_zero start hπ) =
      finiteGlobalContraction hπ data 0 (Nat.zero_le n) := by
  apply pushout.hom_ext
  · change finiteInfinityChart hπ data 0 (Nat.zero_le n) ≫ _ =
      finiteInfinityChart hπ data 0 (Nat.zero_le n) ≫ _
    rw [finiteGlobalInitialIso_infinity_assoc,
      WeierstrassGlobalModification.infinityChart_contraction, finiteInfinityChart_contraction]
  · change finiteLocalChart hπ data 0 (Nat.zero_le n) ≫ _ =
      finiteLocalChart hπ data 0 (Nat.zero_le n) ≫ _
    rw [finiteGlobalInitialIso_local_assoc,
      WeierstrassGlobalModification.localChart_contraction,
      finiteLocalChart_contraction]
    change _ = 𝟙 _ ≫ initialToCurve d₀
    rw [Category.id_comp]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
