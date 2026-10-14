/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchTargetNeighborhood
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Finite etale coefficient neighborhoods covering an arbitrary etale image

Actual affine finite etale branch covers give coefficient neighborhoods of
an arbitrary target. When the original etale projection is surjective, those
coefficient neighborhoods cover the entire target, including its nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchTargetAtlas
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y : Over S}
  (f : X ⟶ Y) [Etale f.left]

/-- Choose constructed schemes and morphisms, with no effectivity hypothesis. -/
def data (x : X.left) : Σ (Z W : Over S), (W ⟶ Y) × (Z ⟶ W) × (Z ⟶ X) :=
  let h := EtaleFiniteBranchTargetNeighborhood.exists_cover f ⊤ ⊤ x (by trivial) (by trivial)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩

/-- The selected branch source. -/
def source (x : X.left) : Over S := (data f x).1

/-- The selected affine coefficient image. -/
def target (x : X.left) : Over S := (data f x).2.1

/-- The coefficient neighborhood's actual etale map to the original target. -/
def base (x : X.left) : target f x ⟶ Y := (data f x).2.2.1

/-- The actual finite etale branch cover. -/
def projection (x : X.left) : source f x ⟶ target f x := (data f x).2.2.2.1

/-- The etale branch neighborhood in the original source. -/
def original (x : X.left) : source f x ⟶ X := (data f x).2.2.2.2

/-- Every chosen branch retains all proved geometry and its prescribed original point. -/
theorem data_spec (x : X.left) :
    IsAffine (source f x).left ∧ IsAffine (target f x).left ∧
      Etale (base f x).left ∧ Etale (projection f x).left ∧
      IsFinite (projection f x).left ∧ Surjective (projection f x).left ∧
      Etale (original f x).left ∧ original f x ≫ f = projection f x ≫ base f x ∧
      ∃ z : (source f x).left, (original f x).left z = x := by
  obtain ⟨z, hZ, hW, hb, ht, hf, hs, ha, hsq, hz, _, _⟩ :=
    (EtaleFiniteBranchTargetNeighborhood.exists_cover f ⊤ ⊤ x
      (by trivial) (by trivial)).choose_spec.choose_spec
      |>.choose_spec.choose_spec.choose_spec
  exact ⟨hZ, hW, hb, ht, hf, hs, ha, hsq, z, hz⟩

instance source_isAffine (x : X.left) : IsAffine (source f x).left := (data_spec f x).1
instance target_isAffine (x : X.left) : IsAffine (target f x).left := (data_spec f x).2.1
instance base_etale (x : X.left) : Etale (base f x).left := (data_spec f x).2.2.1
instance projection_etale (x : X.left) : Etale (projection f x).left :=
  (data_spec f x).2.2.2.1
instance projection_isFinite (x : X.left) : IsFinite (projection f x).left :=
  (data_spec f x).2.2.2.2.1
instance projection_surjective (x : X.left) : Surjective (projection f x).left :=
  (data_spec f x).2.2.2.2.2.1
instance original_etale (x : X.left) : Etale (original f x).left :=
  (data_spec f x).2.2.2.2.2.2.1

/-- The complete scheme square is preserved by every member of the atlas. -/
@[reassoc]
theorem condition (x : X.left) :
    original f x ≫ f = projection f x ≫ base f x := (data_spec f x).2.2.2.2.2.2.2.1

/-- Every original point lies in its actual constructed branch neighborhood. -/
theorem original_covers (x : X.left) :
    ∃ z : (source f x).left, (original f x).left z = x :=
  (data_spec f x).2.2.2.2.2.2.2.2

/-- The constructed affine branches jointly cover the entire original source. -/
def cover : Scheme.Cover.{u} Scheme.etalePrecoverage X.left :=
  Scheme.Cover.mkOfCovers (P := @Etale) X.left
    (fun x ↦ (source f x).left) (fun x ↦ (original f x).left)
    (fun x ↦ ⟨x, original_covers f x⟩) (fun _ ↦ inferInstance)

/-- Surjectivity of the whole original projection makes the coefficient neighborhoods cover. -/
theorem base_covers [Surjective f.left] (y : Y.left) :
    ∃ x : X.left, ∃ z : (target f x).left, (base f x).left z = y := by
  obtain ⟨x, hx⟩ := f.left.surjective y
  obtain ⟨z, hz⟩ := original_covers f x
  refine ⟨x, (projection f x).left z, ?_⟩
  have he := congrArg (fun g : source f x ⟶ Y ↦ g.left z) (condition f x)
  change f.left ((original f x).left z) =
    (base f x).left ((projection f x).left z) at he
  rw [← he, hz, hx]

/-- The actual affine coefficient neighborhoods form an etale cover of the whole target. -/
def targetCover [Surjective f.left] : Scheme.Cover.{u} Scheme.etalePrecoverage Y.left :=
  Scheme.Cover.mkOfCovers (P := @Etale) X.left
    (fun x ↦ (target f x).left) (fun x ↦ (base f x).left)
    (base_covers f) (fun _ ↦ inferInstance)

end FLT.Mazur.EtaleFiniteBranchTargetAtlas
