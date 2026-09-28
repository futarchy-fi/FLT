/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFiltrationLayers

/-!
# Extension from models with generically split order-nine points

The source is an arbitrary chosen model whose geometric generic points split
as a sum of two order-three Galois modules. No integral product presentation is
assumed. Contract the generic quotient, extend the negative generic section by
order-three rigidity, and factor the resulting residual endomorphism through
the flat subgroup closure. This constructs an integral retraction and extends
any generic morphism from the source.

The nonsplit length-two case of `FF.HasOrderThreeFiltration` remains separate.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- A split short exact sequence on geometric generic points. Its maps are
generic only; it includes no integral splitting or morphism-extension hypothesis. -/
structure GenericSplitSequence (S X Q : FF R K) where
  /-- Inclusion of the first generic direct summand. -/
  inclusion : GenericGaloisHom S X
  /-- Projection to the first generic direct summand. -/
  retraction : GenericGaloisHom X S
  /-- Projection to the second generic direct summand. -/
  projection : GenericGaloisHom X Q
  /-- Inclusion of the second generic direct summand. -/
  sectionMap : GenericGaloisHom Q X
  /-- The first inclusion admits the specified generic left inverse. -/
  retract : ∀ s, retraction (inclusion s) = s
  /-- The second projection admits the specified generic right inverse. -/
  sectionProjection : ∀ q, projection (sectionMap q) = q
  /-- The two generic summands recover every generic point of the middle model. -/
  decomposition : ∀ x, inclusion (retraction x) + sectionMap (projection x) = x

/-- The subgroup inclusion in a generic splitting is injective. -/
theorem GenericSplitSequence.inclusion_injective {S X Q : FF R K}
    (E : GenericSplitSequence S X Q) : Function.Injective E.inclusion :=
  Function.LeftInverse.injective E.retract

/-- The quotient projection in a generic splitting is surjective. -/
theorem GenericSplitSequence.projection_surjective {S X Q : FF R K}
    (E : GenericSplitSequence S X Q) : Function.Surjective E.projection :=
  Function.RightInverse.surjective E.sectionProjection

/-- The generic projection kills the first summand. -/
@[simp] theorem GenericSplitSequence.projection_inclusion {S X Q : FF R K}
    (E : GenericSplitSequence S X Q) (s : S.Points) : E.projection (E.inclusion s) = 0 := by
  have h := E.decomposition (E.inclusion s)
  rw [E.retract] at h
  have hz : E.sectionMap (E.projection (E.inclusion s)) = 0 := by
    apply add_left_cancel (a := E.inclusion s)
    simpa only [add_zero] using h
  have he := congrArg E.projection hz
  simpa only [E.sectionProjection, map_zero] using he

/-- The first summand is exactly the kernel of the generic projection. -/
theorem GenericSplitSequence.exact {S X Q : FF R K}
    (E : GenericSplitSequence S X Q) (x : X.Points) :
    E.projection x = 0 ↔ ∃ s, E.inclusion s = x := by
  constructor
  · intro hx
    exact ⟨E.retraction x, by simpa only [hx, map_zero, add_zero] using E.decomposition x⟩
  · rintro ⟨s, rfl⟩
    exact E.projection_inclusion s

variable [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- A split generic extension of order-three groups has a length-two integral filtration. -/
theorem GenericSplitSequence.hasOrderThreeFiltration {S X Q : FF R K}
    (E : GenericSplitSequence S X Q) (hS : Nat.card S.Points = 3)
    (hQ : Nat.card Q.Points = 3) : X.HasOrderThreeFiltration 2 :=
  FF.hasOrderThreeFiltration_of_extension E.inclusion E.projection
    E.inclusion_injective E.projection_surjective E.exact hS hQ

/-- An arbitrary model of a split generic extension of order-three groups has order nine. -/
theorem GenericSplitSequence.card_eq_nine {S X Q : FF R K}
    (E : GenericSplitSequence S X Q) (hS : Nat.card S.Points = 3)
    (hQ : Nat.card Q.Points = 3) : Nat.card X.Points = 9 :=
  (E.hasOrderThreeFiltration hS hQ).card

/-- A generic splitting with order-three quotient gives an integral retraction onto
the flat closure of its first summand. The first summand may have arbitrary order. -/
theorem GenericSplitSequence.exists_integral_retraction
    {S X Q : FF ℤ_[3] ℚ_[3]} (E : GenericSplitSequence S X Q)
    (hQ : Nat.card Q.Points = 3) :
    ∃ r : ModelHom X (E.inclusion.closure E.inclusion_injective),
      ∀ x, genericHom r x = E.retraction x := by
  let QO := E.projection.flatQuotient E.projection_surjective
  let qO : ModelHom X QO := E.projection.toFlatQuotient E.projection_surjective
  let ns : GenericGaloisHom QO X :=
    { toFun := fun q ↦ -E.sectionMap q
      map_zero' := by simp
      map_add' := by intro a b; simp [add_comm]
      map_smul' := by intro σ q; simp }
  obtain ⟨sO, hsO, _⟩ := raynaud_extend_generic_morphism_of_order_three QO X hQ ns
  let d : ModelHom X X := ModelHom.add (BialgHom.id ℤ_[3] X.CoordinateRing) (qO.comp sO)
  have hd : genericHom d = E.inclusion.comp E.retraction := by
    ext x
    change genericHom (ModelHom.add _ _) x = _
    rw [ModelHom.genericHom_add, genericHom_id, genericHom_comp]
    change x + genericHom sO (genericHom (E.projection.toFlatQuotient _) x) = _
    rw [E.projection.genericHom_toFlatQuotient, hsO]
    change x + -E.sectionMap (E.projection x) = E.inclusion (E.retraction x)
    simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq.mpr (E.decomposition x)).symm
  exact ⟨E.inclusion.closureLift E.inclusion_injective d E.retraction hd,
    E.inclusion.genericHom_closureLift E.inclusion_injective d E.retraction hd⟩

/-- Generic maps from an arbitrary model of a split order-nine generic extension
extend uniquely, with no integral product presentation assumed. -/
theorem raynaud_extend_generic_morphism_of_generic_split_order_three
    {S X Q : FF ℤ_[3] ℚ_[3]} (E : GenericSplitSequence S X Q)
    (hS : Nat.card S.Points = 3) (hQ : Nat.card Q.Points = 3)
    (Y : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f := by
  let SO := E.inclusion.closure E.inclusion_injective
  let QO := E.projection.flatQuotient E.projection_surjective
  let qO : ModelHom X QO := E.projection.toFlatQuotient E.projection_surjective
  obtain ⟨rO, hrO⟩ := E.exists_integral_retraction hQ
  let l : GenericGaloisHom SO Y := f.comp E.inclusion
  let r : GenericGaloisHom QO Y := f.comp E.sectionMap
  obtain ⟨lO, hlO, _⟩ := raynaud_extend_generic_morphism_of_order_three SO Y hS l
  obtain ⟨tO, htO, _⟩ := raynaud_extend_generic_morphism_of_order_three QO Y hQ r
  let fO : ModelHom X Y := ModelHom.add (rO.comp lO) (qO.comp tO)
  have hfO : genericHom fO = f := by
    ext x
    change genericHom (ModelHom.add _ _) x = _
    rw [ModelHom.genericHom_add, genericHom_comp, genericHom_comp, hrO, hlO, htO]
    change f (E.inclusion (E.retraction x)) +
      f (E.sectionMap (genericHom (E.projection.toFlatQuotient _) x)) = f x
    rw [E.projection.genericHom_toFlatQuotient, ← map_add, E.decomposition]
  exact ⟨fO, hfO, fun g hg ↦ genericHom_injective X Y (hg.trans hfO.symm)⟩

/-- The first graph projection is surjective for a generically split order-nine source. -/
theorem GenericGaloisHom.graphFst_surjective_of_generic_split_order_three
    {S X Q Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    (E : GenericSplitSequence S X Q)
    (hS : Nat.card S.Points = 3) (hQ : Nat.card Q.Points = 3) :
    Function.Surjective f.graphFst := by
  obtain ⟨g, hg, _⟩ := raynaud_extend_generic_morphism_of_generic_split_order_three E hS hQ Y f
  apply f.graphFst_surjective_of_integral
  intro y
  refine ⟨g y, ?_⟩
  rw [← hg, ModelHom.toBialgHom_genericHom]
  rfl

end ThreeAdicPlan
