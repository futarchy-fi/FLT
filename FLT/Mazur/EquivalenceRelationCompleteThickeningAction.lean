/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteIdealInvariant

/-!
# The moving permutation action on every complete infinitesimal source

Each action is constructed on the full power quotient. Its source inclusion is
equivariant, so its first endpoint and original relation arrow remain unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- The moving permutation restricts to the actual power-quotient source. -/
def completeThickeningActionMap (k : ℕ) (σ : Equiv.Perm I) :
    completeThickening (p := p) (q := q) I o k ⟶
      completeThickening (p := p) (q := q) I o k :=
  Scheme.IdealSheafData.subschemeMap _ _ (action e I o σ).hom
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (completeSupportIdeal_pow_comap_action e I o σ (k + 1)).le)

/-- Stage permutations retain the original inclusion as an exact scheme identity. -/
@[reassoc] theorem completeThickeningActionMap_inclusion (k : ℕ) (σ : Equiv.Perm I) :
    completeThickeningActionMap e I o k σ ≫ completeThickeningInclusion I o k =
      completeThickeningInclusion I o k ≫ (action e I o σ).hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The identity permutation acts identically on every infinitesimal order. -/
theorem completeThickeningActionMap_one (k : ℕ) :
    completeThickeningActionMap e I o k 1 = 𝟙 _ := by
  apply (cancel_mono (completeThickeningInclusion (p := p) (q := q) I o k)).mp
  rw [completeThickeningActionMap_inclusion, Category.id_comp]
  change _ ≫ actionMap e I o 1 = _
  rw [actionMap_one, Category.comp_id]

/-- Multiplication is respected on the entire scheme, including its nilpotents. -/
theorem completeThickeningActionMap_mul (k : ℕ) (σ τ : Equiv.Perm I) :
    completeThickeningActionMap e I o k (σ * τ) =
      completeThickeningActionMap e I o k τ ≫ completeThickeningActionMap e I o k σ := by
  apply (cancel_mono (completeThickeningInclusion (p := p) (q := q) I o k)).mp
  simp only [Category.assoc, completeThickeningActionMap_inclusion,
    completeThickeningActionMap_inclusion_assoc]
  change _ ≫ actionMap e I o (σ * τ) = _
  rw [actionMap_mul]
  rfl

/-- A constructed automorphism of each complete thickening. -/
def completeThickeningActionAut (k : ℕ) (σ : Equiv.Perm I) :
    Aut (completeThickening (p := p) (q := q) I o k) where
  hom := completeThickeningActionMap e I o k σ
  inv := completeThickeningActionMap e I o k σ⁻¹
  hom_inv_id := by
    rw [← completeThickeningActionMap_mul, inv_mul_cancel, completeThickeningActionMap_one]
  inv_hom_id := by
    rw [← completeThickeningActionMap_mul, mul_inv_cancel, completeThickeningActionMap_one]

/-- The finite permutation group acts on each actual infinitesimal source. -/
def completeThickeningAction (k : ℕ) :
    Equiv.Perm I →* Aut (completeThickening (p := p) (q := q) I o k) where
  toFun := completeThickeningActionAut e I o k
  map_one' := by
    apply Aut.ext
    exact completeThickeningActionMap_one e I o k
  map_mul' σ τ := by
    apply Aut.ext
    exact completeThickeningActionMap_mul e I o k σ τ

/-- The stage action follows the same original moving endpoint arrow. -/
@[reassoc] theorem completeThickeningActionMap_first (k : ℕ) (σ : Equiv.Perm I) :
    completeThickeningActionMap e I o k σ ≫ completeThickeningInclusion I o k ≫
        first p q I o =
      completeThickeningInclusion I o k ≫ actionArrow I o σ ≫ q := by
  rw [← Category.assoc, completeThickeningActionMap_inclusion, Category.assoc,
    ← actionArrow_second]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
