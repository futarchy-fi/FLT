/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDiscrepancySeparation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual affine vanishing neighborhoods from ideal-power membership

These are neighborhoods in the scheme carrying the discrepancy. No image of
such a neighborhood under a nonproper morphism is asserted to contain a whole
inverse image of a neighborhood in the target.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme}

/-- Global kernel membership restricts to the exact affine ideal of a quasi-compact map. -/
theorem restrict_mem_kernel (f : Y ⟶ X) [QuasiCompact f]
    (a : Γ(X, ⊤)) (ha : f.appTop a = 0) (V : X.affineOpens) :
    X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op a ∈ f.ker.ideal V := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  change (X.presheaf.map _ ≫ f.app V.1) a = 0
  rw [f.naturality]
  change (Y.presheaf.map _) (f.appTop a) = 0
  rw [ha, map_zero]

/-- An annihilator congruent to one has a basic open containing the full closed support. -/
theorem support_subset_basicOpen (J : X.IdealSheafData) (V : X.affineOpens)
    (s : Γ(X, V)) (hs : 1 - s ∈ J.ideal V) :
    (J.support : Set X) ∩ V.1 ⊆ X.basicOpen s := by
  rintro x ⟨hx, hxV⟩
  have hn : x ∉ X.basicOpen (1 - s) :=
    (X.mem_zeroLocus_iff _ x).mp
      ((J.mem_support_iff_of_mem hxV).mp hx) (1 - s) hs
  have h1 : x ∈ X.basicOpen (1 - s + s) := by
    rw [sub_add_cancel, X.basicOpen_one]
    exact hxV
  exact (X.basicOpen_add_le (1 - s) s h1).resolve_left hn

/-- Multiplication by a unit on its basic open turns the annihilator into actual zero. -/
theorem restrict_eq_zero_of_annihilator (V : X.Opens) (s a : Γ(X, V))
    (ha : s * a = 0) :
    X.presheaf.map (homOfLE (X.basicOpen_le s)).op a = 0 := by
  let r := X.presheaf.map (homOfLE (X.basicOpen_le s)).op
  have hu : IsUnit (r s) := X.toRingedSpace.isUnit_res_basicOpen s
  apply hu.mul_left_cancel
  rw [mul_zero, ← map_mul, ha, map_zero]

/-- Every affine chart has one actual vanishing neighborhood of its whole adic support. -/
theorem exists_affine_neighborhood [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (V : X.affineOpens) (a : Γ(X, V))
    (ha : ∀ n : ℕ, a ∈ J.ideal V ^ (n + 1)) :
    ∃ s : Γ(X, V), 1 - s ∈ J.ideal V ∧
      (J.support : Set X) ∩ V.1 ⊆ X.basicOpen s ∧
      X.presheaf.map (homOfLE (X.basicOpen_le s)).op a = 0 := by
  let _ := IsLocallyNoetherian.component_noetherian V
  obtain ⟨s, hs, hsa⟩ := AdicDiscrepancySeparation.exists_ring_annihilator (J.ideal V) a ha
  exact ⟨s, hs, support_subset_basicOpen J V s hs,
    restrict_eq_zero_of_annihilator V.1 s a hsa⟩

end FLT.Mazur.SchemeAdicVanishingNeighborhood
