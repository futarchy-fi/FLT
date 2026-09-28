/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudOrderThreeFiltration
public import FLT.GroupScheme.RaynaudQuotientFunctoriality

/-!
# Construction and comparison of the order-three layers

Generic subgroup data construct the corresponding integral filtration by flat
closure. A morphism of ambient models restricts to a morphism of their subgroup
closures; order-three rigidity makes this restriction invertible. Together with
the quotient comparison in `RaynaudQuotientFunctoriality`, this handles both
outer terms of an order-nine dévissage diagram, but not its middle term.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- Every order-three model has a length-one finite flat filtration. -/
theorem FF.hasOrderThreeFiltration_of_order_three (X : FF R K)
    (hX : Nat.card X.Points = 3) : X.HasOrderThreeFiltration 1 := by
  let S := X.torsionClosure 1
  let i := X.torsionClosureInclusion 1
  have hS : Nat.card S.Points = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨fun x y ↦ ?_⟩, inferInstance⟩
    apply Subtype.ext
    have hx := x.property
    have hy := y.property
    change 1 • x.val = 0 at hx
    change 1 • y.val = 0 at hy
    rw [one_nsmul] at hx hy
    exact hx.trans hy.symm
  have hi : Function.Injective (genericHom i) := by
    intro x y h
    apply Subtype.ext
    change genericHom (X.torsionClosureInclusion 1) x =
      genericHom (X.torsionClosureInclusion 1) y at h
    simpa only [FF.genericHom_torsionClosureInclusion] using h
  refine ⟨S, i, X.torsionClosureInclusion_surjective 1, hi, ?_, hS⟩
  rw [AddSubgroup.index_eq_card_sub, (genericHom i).card_range hi, hX, hS]

/-- An embedded generic subgroup with an order-three quotient extends a filtration,
using its flat closure inside the specified ambient model. -/
theorem FF.HasOrderThreeFiltration.cons_of_generic_embedding
    {S X : FF R K} {n : ℕ} (hS : S.HasOrderThreeFiltration n)
    (i : GenericGaloisHom S X) (hi : Function.Injective i)
    (hindex : i.toAddMonoidHom.range.index = 3) : X.HasOrderThreeFiltration (n + 1) := by
  let e : GenericGaloisHom S (i.closure hi) :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hc : genericHom (i.closureInclusion hi) = i := by
    ext x
    exact i.genericHom_closureInclusion hi x
  refine ⟨i.closure hi, i.closureInclusion hi, Ideal.Quotient.mk_surjective,
    ?_, ?_, hS.of_generic_bijective e Function.bijective_id⟩
  · simpa only [hc] using hi
  · simpa only [hc] using hindex

omit [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K] in
/-- The generic quotient in a short exact sequence has the index of the subgroup. -/
theorem GenericGaloisHom.index_range_of_exact {S X Q : FF R K}
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q)
    (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) :
    i.toAddMonoidHom.range.index = Nat.card Q.Points := by
  have hr : i.toAddMonoidHom.range = q.toAddMonoidHom.ker := by
    ext x
    exact (hexact x).symm
  rw [hr, AddSubgroup.index_ker]
  exact Nat.card_congr (Equiv.ofBijective
    (fun x : q.toAddMonoidHom.range ↦ x.val)
    ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, hq y⟩, rfl⟩⟩)

/-- Any generic extension of two order-three groups gives a length-two integral
filtration on every chosen model of the middle group. No generic splitting is required. -/
theorem FF.hasOrderThreeFiltration_of_extension
    {S X Q : FF R K} (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (hS : Nat.card S.Points = 3) (hQ : Nat.card Q.Points = 3) :
    X.HasOrderThreeFiltration 2 :=
  (S.hasOrderThreeFiltration_of_order_three hS).cons_of_generic_embedding i hi
    ((i.index_range_of_exact q hq hexact).trans hQ)

/-- Restrict an integral map to the flat closures of an embedded generic subgroup. -/
def GenericGaloisHom.closureMap {S X Y : FF R K}
    (i : GenericGaloisHom S X) (hi : Function.Injective i) (g : ModelHom X Y)
    (hj : Function.Injective ((genericHom g).comp i)) :
    ModelHom (i.closure hi)
      (GenericGaloisHom.closure (X := S) (Y := Y) ((genericHom g).comp i) hj) := by
  let j : GenericGaloisHom S Y := (genericHom g).comp i
  let e : GenericGaloisHom (i.closure hi) S :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact j.closureLift hj ((i.closureInclusion hi).comp g) e (by
    ext s
    rw [genericHom_comp, i.genericHom_closureInclusion]
    rfl)

/-- Subgroup restriction commutes with the closed immersions of both closures. -/
@[simp] theorem GenericGaloisHom.closureMap_comp_inclusion {S X Y : FF R K}
    (i : GenericGaloisHom S X) (hi : Function.Injective i) (g : ModelHom X Y)
    (hj : Function.Injective ((genericHom g).comp i)) :
    (i.closureMap hi g hj).comp
      (GenericGaloisHom.closureInclusion (X := S) (Y := Y) ((genericHom g).comp i) hj) =
      (i.closureInclusion hi).comp g := by
  ext a
  rfl

/-- The comparison of subgroup closures is the identity on their prescribed point group. -/
@[simp] theorem GenericGaloisHom.genericHom_closureMap {S X Y : FF R K}
    (i : GenericGaloisHom S X) (hi : Function.Injective i) (g : ModelHom X Y)
    (hj : Function.Injective ((genericHom g).comp i)) (s : S.Points) :
    genericHom (i.closureMap hi g hj) s = s := by
  apply hj
  have he := congrArg (fun k : ModelHom (i.closure hi) Y ↦ genericHom k s)
    (i.closureMap_comp_inclusion hi g hj)
  rw [genericHom_comp, genericHom_comp, GenericGaloisHom.genericHom_closureInclusion,
    i.genericHom_closureInclusion] at he
  exact he

/-- Subgroup comparison maps are injective on integral coordinate rings. -/
theorem GenericGaloisHom.closureMap_injective {S X Y : FF R K}
    (i : GenericGaloisHom S X) (hi : Function.Injective i) (g : ModelHom X Y)
    (hj : Function.Injective ((genericHom g).comp i)) :
    Function.Injective (i.closureMap hi g hj) := by
  apply ModelHom.injective_of_baseChange_injective
  rw [← ModelHom.toBialgHom_genericHom]
  apply GenericGaloisHom.toBialgHom_injective
  exact fun s ↦ ⟨s, i.genericHom_closureMap hi g hj s⟩

/-- Order-three rigidity makes the subgroup comparison an integral isomorphism. -/
theorem GenericGaloisHom.closureMap_bijective_of_order_three
    {S X Y : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (hi : Function.Injective i) (g : ModelHom X Y)
    (hj : Function.Injective ((genericHom g).comp i)) (hS : Nat.card S.Points = 3) :
    Function.Bijective (i.closureMap hi g hj) := by
  have h := i.closureMap_injective hi g hj
  exact ⟨h, raynaud_integral_rigidity_of_order_three
    (GenericGaloisHom.closure (X := S) (Y := Y) ((genericHom g).comp i) hj) (i.closure hi)
    hS hS _ h⟩

end ThreeAdicPlan
