/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.ReverseExtHypothesis
public import FLT.GroupScheme.StableSubgroupExtension

/-!
# Category D and integral exact subquotients

The category-D conditions pass through injective and surjective equivariant
point maps. Applied to an integral extension, this retains category D for both
ends while preserving the specified integral maps and torsor data.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- Category D passes to an equivariantly embedded point subgroup. -/
theorem InCategoryD.ofInjective {A H : FiniteFlatObject ZInvTwo}
    (hH : InCategoryD H) (i : A.points →+[Γ] H.points) (hi : Function.Injective i) :
    InCategoryD A := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hH.threePrimary
    have hd := AddSubgroup.card_dvd_of_injective i.toAddMonoidHom hi
    rw [hn] at hd
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hd
    exact ⟨m, hm⟩
  · intro σ hσ a
    apply hi
    simpa only [map_sub, map_smul, map_zero] using hH.inertiaSquareZero σ hσ (i a)

/-- Category D passes to an equivariant quotient of its point group. -/
theorem InCategoryD.ofSurjective {H Q : FiniteFlatObject ZInvTwo}
    (hH : InCategoryD H) (q : H.points →+[Γ] Q.points) (hq : Function.Surjective q) :
    InCategoryD Q := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hH.threePrimary
    have hd := AddSubgroup.card_dvd_of_surjective q.toAddMonoidHom hq
    rw [hn] at hd
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hd
    exact ⟨m, hm⟩
  · intro σ hσ y
    obtain ⟨x, rfl⟩ := hq y
    simpa only [map_sub, map_smul, map_zero] using
      congrArg q (hH.inertiaSquareZero σ hσ x)

/-- The integral kernel of a category-D extension belongs to category D. -/
theorem FiniteFlatExtension.inCategoryDLeft {A H Q : FiniteFlatObject ZInvTwo}
    (E : FiniteFlatExtension A H Q) (hH : InCategoryD H) : InCategoryD A :=
  hH.ofInjective (FiniteFlatObject.pointMap E.inclusion) E.pointsInjective

/-- The integral quotient of a category-D extension belongs to category D. -/
theorem FiniteFlatExtension.inCategoryDRight {A H Q : FiniteFlatObject ZInvTwo}
    (E : FiniteFlatExtension A H Q) (hH : InCategoryD H) : InCategoryD Q :=
  hH.ofSurjective (FiniteFlatObject.pointMap E.quotient) E.pointsSurjective

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- Exactness identifies the point kernel with the image of the integral inclusion. -/
theorem FiniteFlatExtension.pointKernelEqRange {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) :
    (FiniteFlatObject.pointMap E.quotient).toAddMonoidHom.ker =
      (FiniteFlatObject.pointMap E.inclusion).toAddMonoidHom.range := by
  ext x
  exact E.pointsExact x

/-- The orders of the two ends of an integral extension multiply to the middle order. -/
theorem FiniteFlatExtension.cardPoints {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) :
    Nat.card A.points * Nat.card Q.points = Nat.card H.points := by
  let i := (FiniteFlatObject.pointMap E.inclusion).toAddMonoidHom
  let q := (FiniteFlatObject.pointMap E.quotient).toAddMonoidHom
  have hi : Nat.card i.range = Nat.card A.points :=
    (Nat.card_congr (Equiv.ofInjective i E.pointsInjective)).symm
  have hq : q.ker.index = Nat.card Q.points :=
    by
      rw [AddSubgroup.index_ker q, AddMonoidHom.range_eq_top.mpr E.pointsSurjective]
      exact Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup Q.points) ≃+ Q.points).toEquiv
  rw [← hi, ← E.pointKernelEqRange, ← hq]
  exact q.ker.card_mul_index

/-- A nonzero kernel makes the order of the quotient strictly smaller. -/
theorem FiniteFlatExtension.cardRightLt {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) [Nontrivial A.points] :
    Nat.card Q.points < Nat.card H.points := by
  rw [← E.cardPoints]
  have hA : 1 < Nat.card A.points := Finite.one_lt_card
  have hQ : 0 < Nat.card Q.points := Nat.card_pos
  nlinarith

/-- A model with one geometric point has the coordinate algebra of the zero group. -/
def FiniteFlatObject.zeroCoordinatesEquiv [IsFractionRing R ℚ]
    (H : FiniteFlatObject R) [Subsingleton H.points] : H.model.CoordinateRing ≃ₐ[R] R := by
  have h : ModelHom.zero H.toFF H.toFF = BialgHom.id R H.model.CoordinateRing := by
    apply genericHom_injective H.toFF H.toFF
    ext x
    exact Subsingleton.elim (α := H.points) _ _
  have hc (a : H.model.CoordinateRing) :
      algebraMap R H.model.CoordinateRing (Coalgebra.counit (R := R) a) = a :=
    DFunLike.congr_fun h a
  apply AlgEquiv.ofBijective (Bialgebra.counitAlgHom R H.model.CoordinateRing)
  exact ⟨fun a b hab ↦ (hc a).symm.trans ((congrArg (algebraMap R _) hab).trans (hc b)),
    fun r ↦ ⟨algebraMap R _ r, Bialgebra.counit_algebraMap r⟩⟩

end ThreeAdicPlan
