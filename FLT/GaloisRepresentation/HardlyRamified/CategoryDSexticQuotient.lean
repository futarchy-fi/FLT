/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFieldDegree
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDSimpleRepresentation
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

/-!
# The actual sextic quotient acting on a simple category-D object

The full augmented point-action kernel gives a finite quotient of the rational
Galois group. Under the explicit discriminant estimate this quotient has order
six, so a subgroup of order three is normal and the quotient has order two.
The original object's point action factors through this concrete quotient.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The finite quotient cut out by the full augmented point action. -/
abbrev AugmentedPointGaloisGroup (H : FiniteFlatObject ZInvTwo) :=
  Γ ⧸ (augmentedObject H).points.pointActionKernel

/-- Galois correspondence identifies the actual point quotient with the
Galois group of the augmented field. -/
def augmentedPointGaloisEquiv (H : FiniteFlatObject ZInvTwo) :
    AugmentedPointGaloisGroup H ≃* (AugmentedField H ≃ₐ[ℚ] AugmentedField H) := by
  have : ((augmentedObject H).points.closedPointActionKernel : Subgroup Γ).Normal :=
    inferInstanceAs (augmentedObject H).points.pointActionKernel.Normal
  exact InfiniteGalois.normalAutEquivQuotient (augmentedObject H).points.closedPointActionKernel

instance (H : FiniteFlatObject ZInvTwo) : Finite (AugmentedPointGaloisGroup H) :=
  Finite.of_equiv _ (augmentedPointGaloisEquiv H).toEquiv.symm

/-- The order of the actual augmented quotient is the field degree. -/
theorem augmentedPointGaloisGroup_card (H : FiniteFlatObject ZInvTwo) :
    Nat.card (AugmentedPointGaloisGroup H) = Module.finrank ℚ (AugmentedField H) := by
  rw [Nat.card_congr (augmentedPointGaloisEquiv H).toEquiv,
    IsGalois.card_aut_eq_finrank]

/-- The action of the augmented quotient on the original point group. -/
def augmentedPointRepresentation (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] : Representation (ZMod 3) (AugmentedPointGaloisGroup H) H.points :=
  QuotientGroup.lift _ H.threeRepresentation (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    ext w
    have h := ((augmentedObject H).points.mem_pointActionKernel σ).mp hσ (w, 0)
    exact congrArg Prod.fst h)

/-- Pulling the quotient action back gives exactly the original Galois action. -/
theorem augmentedPointRepresentation_apply (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (σ : Γ) (w : H.points) :
    augmentedPointRepresentation H (QuotientGroup.mk' _ σ) w = σ • w := rfl

/-- Every group of order six has a normal subgroup of order three and quotient
of order two. -/
theorem exists_normal_threeSubgroup_of_card_eq_six {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 6) :
    ∃ P : Subgroup G, P.Normal ∧ IsPGroup 3 P ∧ Nat.card (G ⧸ P) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) 3
    (n := 1) (by simp [hG])
  have hP3 : Nat.card P = 3 := by simpa using hP
  have hm := P.card_mul_index
  rw [hP3, hG] at hm
  have hi : P.index = 2 := by omega
  exact ⟨P, P.normal_of_index_eq_two hi, IsPGroup.of_card hP, hi⟩

/-- Under the discriminant estimate, the actual quotient acting on `H.points`
has the required normal three-subgroup and quotient of order two. -/
theorem augmentedPointGaloisGroup_normal_threeSubgroup
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) :
    ∃ P : Subgroup (AugmentedPointGaloisGroup H),
      P.Normal ∧ IsPGroup 3 P ∧ Nat.card (AugmentedPointGaloisGroup H ⧸ P) = 2 := by
  apply exists_normal_threeSubgroup_of_card_eq_six
  rw [augmentedPointGaloisGroup_card,
    augmentedField_finrank_eq_six_of_discriminantBound hs hD hdisc]

/-- Conditional generic-point classification using the actual arithmetic
quotient. The discriminant estimate is the only additional arithmetic input. -/
theorem Simple.points_three_of_discriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) :
    letI := hs.threeModule hD
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ,
        (∀ σ, χ σ = 1 ∨ χ σ = -1) ∧
        (∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w) := by
  let := hs.threeModule hD
  obtain ⟨P, hnormal, hP, hcard⟩ :=
    augmentedPointGaloisGroup_normal_threeSubgroup hs hD hdisc
  let : P.Normal := hnormal
  exact hs.points_three_of_normal_threeSubgroup (augmentedPointRepresentation H)
    (QuotientGroup.mk' _) (augmentedPointRepresentation_apply H) P hP (hcard ▸ dvd_rfl)

end ThreeAdicPlan
