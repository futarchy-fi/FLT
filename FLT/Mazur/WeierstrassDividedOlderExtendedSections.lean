/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalSections
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension

/-!
# The ordered first sections in the actual extended global model

Both middle-node origins remain the two distinct ordered sections after any
nonzero coefficient extension. Their sections are constructed in the actual
global coefficient pullback, and each lifts to the entire corresponding node.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "first" => olderGlobalFirstSection hπ data D j hj r hr hk0 hk
local notation "second" => olderGlobalSecondSection hπ data D j hj r hr hk0 hk

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "H" => globalResidueExtensionMap_isPullback hπ data S (j + 1 + r) hr

/-- The first ordered section of the actual extended global model. -/
def olderExtendedFirstSection : Spec (.of S) ⟶
    finiteGlobalTensorModel hπ data S (j + 1 + r) hr :=
  (H).lift (𝟙 _) (e ≫ first) (by
    rw [Category.id_comp, Category.assoc, olderGlobalFirstSection_structure,
      Category.comp_id])

/-- The opposite ordered section of the actual extended global model. -/
def olderExtendedSecondSection : Spec (.of S) ⟶
    finiteGlobalTensorModel hπ data S (j + 1 + r) hr :=
  (H).lift (𝟙 _) (e ≫ second) (by
    rw [Category.id_comp, Category.assoc, olderGlobalSecondSection_structure,
      Category.comp_id])

/-- The first extended section keeps its precise original ordering. -/
@[reassoc] theorem olderExtendedFirstSection_projection :
    olderExtendedFirstSection hπ data D j hj r hr hk0 hk S ≫ p = e ≫ first :=
  (H).lift_snd _ _ _

/-- The second extended section keeps its precise original ordering. -/
@[reassoc] theorem olderExtendedSecondSection_projection :
    olderExtendedSecondSection hπ data D j hj r hr hk0 hk S ≫ p = e ≫ second :=
  (H).lift_snd _ _ _

/-- The first extended map is a section over the new coefficient ring. -/
@[reassoc] theorem olderExtendedFirstSection_structure :
    olderExtendedFirstSection hπ data D j hj r hr hk0 hk S ≫ pullback.fst qS f =
      𝟙 (Spec (.of S)) := (H).lift_fst _ _ _

/-- The second extended map is a section over the new coefficient ring. -/
@[reassoc] theorem olderExtendedSecondSection_structure :
    olderExtendedSecondSection hπ data D j hj r hr hk0 hk S ≫ pullback.fst qS f =
      𝟙 (Spec (.of S)) := (H).lift_fst _ _ _

/-- No nonzero extension identifies the two ordered global sections. -/
theorem olderExtendedSections_ne [Nontrivial S] :
    olderExtendedFirstSection hπ data D j hj r hr hk0 hk S ≠
      olderExtendedSecondSection hπ data D j hj r hr hk0 hk S := by
  intro h
  have hp := congrArg (fun t => t ≫ p) h
  rw [olderExtendedFirstSection_projection, olderExtendedSecondSection_projection] at hp
  exact olderGlobalSections_extension_ne hπ data D j hj r hr hk0 hk S hp

end FLT.Mazur.WeierstrassDividedDepth
