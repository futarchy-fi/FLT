/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenNorm
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Gluing norms from independent finite free charts

The affine target cover need not be invariant under any relation. Its local
bases may have different ranks. Cartesian restriction proves compatibility
on overlaps, so the structure sheaf supplies a unique global norm.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineNormGluing
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]

/-- The norm of a global source section, computed on one actual affine target open. -/
def chart (U : Y.affineOpens) (s : Γ(X, ⊤)) : Γ(Y, U.1) :=
  AffineOpenNorm.norm f U (X.presheaf.map (homOfLE le_top).op s)

omit [IsAffine Y] in
/-- A chart norm restricts to the norm of the same global source section. -/
theorem chart_restrict {U V : Y.affineOpens} (hU : AffineOpenNorm.HasBasis f U)
    (h : V ≤ U) (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE h).op (chart f U s) = chart f V s := by
  rw [chart, AffineOpenNorm.norm_restrict f hU h]
  unfold chart
  congr 1
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp
    (homOfLE le_top).op (homOfLE (f.preimage_mono h)).op) s).symm

/-- Two independent local bases yield compatible norms on their common affine open. -/
theorem chart_overlap (U V : Y.affineOpens)
    (hU : AffineOpenNorm.HasBasis f U) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE inf_le_left).op (chart f U s) =
      Y.presheaf.map (homOfLE inf_le_right).op (chart f V s) := by
  let W : Y.affineOpens := ⟨U.1 ⊓ V.1, U.2.inf V.2⟩
  have h₁ : W ≤ U := show U.1 ⊓ V.1 ≤ U.1 from inf_le_left
  have h₂ : W ≤ V := show U.1 ⊓ V.1 ≤ V.1 from inf_le_right
  exact (chart_restrict f (V := W) hU h₁ s).trans
    (chart_restrict f (V := W) hV h₂ s).symm

variable {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

include hU hcover in
/-- Actual local determinant norms glue uniquely in the original structure sheaf. -/
theorem existsUnique_norm (s : Γ(X, ⊤)) :
    ∃! t : Γ(Y, ⊤), ∀ i,
      Y.presheaf.map (homOfLE le_top).op t = chart f (U i) s := by
  exact Y.sheaf.existsUnique_gluing' (fun i ↦ (U i).1) ⊤
    (fun _ ↦ homOfLE le_top) (ge_of_eq hcover) (fun i ↦ chart f (U i) s)
    (fun i j ↦ chart_overlap f (U i) (U j) (hU i) (hU j) s)

/-- The norm constructed from a cover of the entire original target. -/
def norm (s : Γ(X, ⊤)) : Γ(Y, ⊤) := (existsUnique_norm f U hU hcover s).choose

/-- The glued norm recovers every prescribed local determinant. -/
theorem norm_chart (s : Γ(X, ⊤)) (i : ι) :
    Y.presheaf.map (homOfLE le_top).op (norm f U hU hcover s) = chart f (U i) s :=
  (existsUnique_norm f U hU hcover s).choose_spec.1 i

/-- Equality with the norm is detected on the given cover. -/
theorem eq_norm (s : Γ(X, ⊤)) (t : Γ(Y, ⊤))
    (ht : ∀ i, Y.presheaf.map (homOfLE le_top).op t = chart f (U i) s) :
    t = norm f U hU hcover s :=
  (existsUnique_norm f U hU hcover s).choose_spec.2 t ht

/-- The glued norm preserves multiplication. -/
theorem norm_mul (s t : Γ(X, ⊤)) :
    norm f U hU hcover (s * t) = norm f U hU hcover s * norm f U hU hcover t := by
  symm
  apply eq_norm
  intro i
  rw [map_mul, norm_chart, norm_chart]
  simp only [chart, map_mul, AffineOpenNorm.norm_mul]

/-- The glued norm sends one to one even when ranks vary between charts. -/
theorem norm_one : norm f U hU hcover 1 = 1 := by
  symm
  apply eq_norm
  intro i
  simp only [chart, map_one, AffineOpenNorm.norm_one]

end FLT.Mazur.AffineNormGluing
