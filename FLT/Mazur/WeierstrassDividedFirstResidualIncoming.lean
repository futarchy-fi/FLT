/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstResidualOrientation
public import FLT.Mazur.WeierstrassDividedRetainedPuncturePreimage

/-!
# The original incoming maps survive the residual correction

The full retained normalization carries the original incoming open to the
incoming puncture. Factoring through that open proves exact equality of
morphisms, without replacing the original Laurent parameter by its tangent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticRetainedFixedSmoothingIso
  arithmeticFirstResidualRetainedIso arithmeticFirstResidualOrientedIso
/-- A morphism into a fixed open is fixed on its entire source scheme. -/
theorem comp_eq_of_fixed_open {U X Y : Scheme} (i : U ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ X) (hi : i ≫ f = i) (g : Y ⟶ X) (hg : Set.range g ⊆ Set.range i) :
    g ≫ f = g := by
  have h := IsOpenImmersion.lift_fac i g hg
  rw [← h, Category.assoc, hi]

/-- A preimage description gives containment of the entire composite range. -/
theorem range_comp_subset_of_preimage {U X Y : Scheme} (f : U ⟶ X) (g : X ⟶ Y)
    (s : Set Y) (h : g ⁻¹' s = Set.range f) : Set.range (f ≫ g) ⊆ s := by
  rintro z ⟨x, rfl⟩
  change g (f x) ∈ s
  change f x ∈ g ⁻¹' s
  rw [h]
  exact ⟨x, rfl⟩

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "t" => parameter R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "N" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
local notation "A" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "C" => arithmeticFirstResidualOrientedIso hπ data H j hj u hu

/-- The original incoming arrow is fixed after full normalization and correction. -/
@[reassoc] theorem arithmeticFirstResidualIncoming_fixed (a : Fin (j + 1)) (b : Bool) :
    (rightBranchOpen Q t ≫ (N a).hom) ≫ (A b).hom =
      rightBranchOpen Q t ≫ (N a).hom :=
  comp_eq_of_fixed_open (rightBranchOpen Q τ) (A b).hom
    (arithmeticFirstResidualRetainedIso_opposite hπ data H j hj u hu b) _
    (range_comp_subset_of_preimage (rightBranchOpen Q t) (N a).hom _
      (arithmeticRetainedFixedSmoothingIso_right_preimage data H 1 (j + 1) hj a))

/-- The inverse correction also fixes the full original incoming arrow. -/
@[reassoc] theorem arithmeticFirstResidualIncoming_fixed_inv (a : Fin (j + 1)) (b : Bool) :
    (rightBranchOpen Q t ≫ (N a).hom) ≫ (A b).inv =
      rightBranchOpen Q t ≫ (N a).hom := by
  apply (cancel_mono (A b).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, arithmeticFirstResidualIncoming_fixed]

/-- Both original first-edge maps are unchanged in the labeled orientation. -/
@[reassoc] theorem arithmeticFirstResidualIncoming_oriented (a : Fin (j + 1)) (b : Bool) :
    (rightBranchOpen Q t ≫ (N a).hom ≫ (O b).hom) ≫ (C b).inv =
      rightBranchOpen Q t ≫ (N a).hom ≫ (O b).hom := by
  have h := congrArg (fun f ↦ f ≫ (O b).hom)
    (arithmeticFirstResidualIncoming_fixed_inv hπ data H j hj u hu a b)
  simpa only [Category.assoc, arithmeticFirstResidualOrientedIso_inv] using h

/-- Both original adjacent incoming maps, including their inversion, are unchanged. -/
@[reassoc] theorem arithmeticFirstResidualPreceding_oriented (a : Fin (j + 1)) (b : Bool) :
    (precedingBranch Q t ≫ (N a).hom ≫ (O b).hom) ≫ (C b).inv =
      precedingBranch Q t ≫ (N a).hom ≫ (O b).hom := by
  have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
    (arithmeticFirstResidualIncoming_oriented hπ data H j hj u hu a b)
  simpa only [precedingBranch, Category.assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
