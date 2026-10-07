/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicIncidence

/-! # Fibers of the cyclic incidence family

The actual incidence embedding identifies every geometric fiber with
the subgroup classified by its parameter. In particular every prime-level
fiber has p points. No group law on the family is assumed in this argument.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonObj
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u

/-- A field-valued point of a disjoint union factors through one of its components. -/
theorem fieldPoint_coprod_cases (K : Type u) [Field K] (X Y : Scheme.{u})
    (f : Spec (.of K) ⟶ X ⨿ Y) :
    (∃ g : Spec (.of K) ⟶ X, g ≫ coprod.inl = f) ∨
      (∃ g : Spec (.of K) ⟶ Y, g ≫ coprod.inr = f) := by
  classical
  let z : Spec (.of K) := Classical.choice inferInstance
  obtain ⟨x, hx⟩ := (coprodMk X Y).surjective (f z)
  cases x with
  | inl x =>
    left
    have hr : Set.range f ⊆ Set.range (coprod.inl : X ⟶ X ⨿ Y) := by
      rintro _ ⟨t, rfl⟩
      exact ⟨x, by simpa only [Subsingleton.elim t z, coprodMk_inl] using hx⟩
    exact ⟨IsOpenImmersion.lift coprod.inl f hr, IsOpenImmersion.lift_fac _ _ _⟩
  | inr x =>
    right
    have hr : Set.range f ⊆ Set.range (coprod.inr : Y ⟶ X ⨿ Y) := by
      rintro _ ⟨t, rfl⟩
      exact ⟨x, by simpa only [Subsingleton.elim t z, coprodMk_inr] using hx⟩
    exact ⟨IsOpenImmersion.lift coprod.inr f hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- A fiber of a coproduct with the base consists of zero and a fiber of the other part. -/
def coprodSectionFiberEquiv (K : Type u) [Field K] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (q : Spec (.of K) ⟶ X) :
    Option {y : Spec (.of K) ⟶ Y // y ≫ f = q} ≃
      {z : Spec (.of K) ⟶ X ⨿ Y // z ≫ coprod.desc (𝟙 X) f = q} :=
  Equiv.ofBijective
    (fun o => o.elim ⟨q ≫ coprod.inl, by simp⟩
      (fun y => ⟨y.val ≫ coprod.inr, by simpa using y.property⟩)) (by
    constructor
    · intro a b h
      have he := congrArg Subtype.val h
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          have h' := congrArg (fun g : Spec (.of K) ⟶ X ⨿ Y =>
            g (IsLocalRing.closedPoint K)) he
          exact (inl_ne_inr X Y _ _ h').elim
      | some a =>
        cases b with
        | none =>
          have h' := congrArg (fun g : Spec (.of K) ⟶ X ⨿ Y =>
            g (IsLocalRing.closedPoint K)) he
          exact (inr_ne_inl X Y _ _ h').elim
        | some b =>
          exact congrArg some (Subtype.ext ((cancel_mono coprod.inr).mp he))
    · rintro ⟨z, hz⟩
      rcases fieldPoint_coprod_cases K X Y z with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · simp only [Category.assoc, coprod.inl_desc, Category.comp_id] at hz
        exact ⟨none, Subtype.ext (congrArg (fun h => h ≫ coprod.inl) hz.symm)⟩
      · exact ⟨some ⟨g, by simpa using hz⟩, rfl⟩)

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]
variable (K : Type u) [Field K] [Algebra R K]

/-- Generator fibers can be expressed by scheme maps or maps over the coefficient base. -/
def cyclicGeneratorFiberEquiv
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    {y : pointSource K ⟶ nonzeroTorsionModel W p // y ≫ scalarQuotientMap W p = q} ≃
      {y : Spec (.of K) ⟶ (nonzeroTorsionModel W p).left //
        y ≫ (scalarQuotientMap W p).left = q.left} where
  toFun y := ⟨y.val.left, congrArg Over.Hom.left y.property⟩
  invFun y := ⟨Over.homMk y.val (by
    rw [← (scalarQuotientMap W p).w, ← Category.assoc, y.property, q.w]),
    Over.OverMorphism.ext y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The incidence fiber consists of zero and the nonzero generators over its parameter. -/
def cyclicIncidenceFiberEquiv
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    Option {y : pointSource K ⟶ nonzeroTorsionModel W p //
      y ≫ scalarQuotientMap W p = q} ≃
      {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
        z ≫ cyclicIncidenceToBase W p = q.left} :=
  (Equiv.optionCongr (cyclicGeneratorFiberEquiv W p K q)).trans
    (coprodSectionFiberEquiv K (scalarQuotientMap W p).left q.left)

/-- Every geometric prime-level incidence fiber has exactly p points. -/
theorem cyclicIncidenceFiber_card [IsAlgClosed K]
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    Nat.card {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = q.left} = p := by
  classical
  obtain ⟨x, rfl⟩ := scalarQuotientFieldPoint_surjective W p K q
  let e := (Equiv.optionCongr (scalarQuotientGeneratorFiberEquiv W p K x)).trans
    (cyclicIncidenceFiberEquiv W p K (x ≫ scalarQuotientMap W p))
  rw [← Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_units, ZMod.card]
  exact Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le

/-- The actual torsion point associated with an incidence fiber point. -/
def cyclicIncidenceTorsionPoint
    (q : pointSource K ⟶ scalarQuotientModel W p)
    (z : {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = q.left}) :
    pointSource K ⟶ torsionModel W p :=
  Over.homMk (z.val ≫ cyclicIncidenceInclusion W p ≫ pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    rw [← Category.assoc (cyclicIncidenceInclusion W p),
      cyclicIncidenceInclusion_toBase, ← Category.assoc, z.property, q.w])

omit [Fact p.Prime] in
/-- The incidence embedding is injective on torsion-valued fiber points. -/
theorem cyclicIncidenceTorsionPoint_injective
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    Function.Injective (cyclicIncidenceTorsionPoint W p K q) := by
  have := cyclicIncidenceInclusion_open W p
  intro a b h
  apply Subtype.ext
  apply (cancel_mono (cyclicIncidenceInclusion W p)).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, cyclicIncidenceInclusion_toBase] using
      a.property.trans b.property.symm
  · exact congrArg Over.Hom.left h

omit [Fact p.Prime] in
/-- The zero component gives the identity torsion point. -/
@[simp] theorem cyclicIncidenceTorsionPoint_zero
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    cyclicIncidenceTorsionPoint W p K q
      (cyclicIncidenceFiberEquiv W p K q none) = 1 := by
  apply Over.OverMorphism.ext
  change (q.left ≫ coprod.inl) ≫
    cyclicIncidenceInclusion W p ≫ pullback.snd _ _ = _
  simp only [Category.assoc, cyclicIncidenceInclusion, coprod.inl_desc_assoc,
    cyclicIncidenceZero, pullback.lift_snd]
  rw [← Category.assoc, q.w]
  rfl

omit [Fact p.Prime] in
/-- The generator component recovers its actual torsion point. -/
@[simp] theorem cyclicIncidenceTorsionPoint_generator
    (q : pointSource K ⟶ scalarQuotientModel W p)
    (y : {y : pointSource K ⟶ nonzeroTorsionModel W p //
      y ≫ scalarQuotientMap W p = q}) :
    cyclicIncidenceTorsionPoint W p K q
      (cyclicIncidenceFiberEquiv W p K q (some y)) =
      y.val ≫ nonzeroTorsionInclusion W p := by
  apply Over.OverMorphism.ext
  change (y.val.left ≫ coprod.inr) ≫
    cyclicIncidenceInclusion W p ≫ pullback.snd _ _ = _
  simp [cyclicIncidenceInclusion, cyclicIncidenceGenerator]

variable [DecidableEq K] [IsAlgClosed K]

/-- The classical elliptic-curve point of an incidence fiber point. -/
def cyclicIncidenceClassicalPoint
    (q : pointSource K ⟶ scalarQuotientModel W p)
    (z : {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = q.left}) :
    (W.map (algebraMap R K)).toAffine.Point :=
  (classicalTorsionMulEquiv W K p (cyclicIncidenceTorsionPoint W p K q z)).toAdd.val

/-- An incidence point belongs to the subgroup classified by its parameter. -/
theorem cyclicIncidenceClassicalPoint_mem
    (q : pointSource K ⟶ scalarQuotientModel W p)
    (z : {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = q.left}) :
    cyclicIncidenceClassicalPoint W p K q z ∈
      (scalarQuotientPrimeSubgroupEquiv W p K q).val := by
  obtain ⟨o, rfl⟩ := (cyclicIncidenceFiberEquiv W p K q).surjective z
  cases o with
  | none =>
    simp only [cyclicIncidenceClassicalPoint, cyclicIncidenceTorsionPoint_zero, map_one]
    exact AddSubgroup.zero_mem _
  | some y =>
    have hy := scalarQuotientPrimeSubgroupEquiv_generator W p K y.val
    rw [y.property] at hy
    rw [hy]
    change (classicalTorsionMulEquiv W K p
      (cyclicIncidenceTorsionPoint W p K q
        (cyclicIncidenceFiberEquiv W p K q (some y)))).toAdd.val ∈ _
    rw [cyclicIncidenceTorsionPoint_generator]
    exact AddSubgroup.mem_zmultiples _

omit [Fact p.Prime] [IsAlgClosed K] in
/-- Distinct incidence fiber points give distinct classical points. -/
theorem cyclicIncidenceClassicalPoint_injective
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    Function.Injective (cyclicIncidenceClassicalPoint W p K q) := by
  intro a b h
  apply cyclicIncidenceTorsionPoint_injective W p K q
  apply (classicalTorsionMulEquiv W K p).injective
  exact Subtype.ext h

/-- The actual geometric incidence fiber is the classified prime-order subgroup. -/
def cyclicIncidenceSubgroupEquiv
    (q : pointSource K ⟶ scalarQuotientModel W p) :
    {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = q.left} ≃
      (scalarQuotientPrimeSubgroupEquiv W p K q).val := by
  let H := (scalarQuotientPrimeSubgroupEquiv W p K q).val
  have hc : Nat.card H = p := (scalarQuotientPrimeSubgroupEquiv W p K q).property
  letI : Finite H := Nat.finite_of_card_ne_zero (hc ▸ (Fact.out : p.Prime).ne_zero)
  let f : {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = q.left} → H :=
    fun z => ⟨cyclicIncidenceClassicalPoint W p K q z,
      cyclicIncidenceClassicalPoint_mem W p K q z⟩
  exact Equiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨fun _ _ h => cyclicIncidenceClassicalPoint_injective W p K q
      (congrArg (fun z : H => z.val) h),
      (cyclicIncidenceFiber_card W p K q).trans hc.symm⟩)

end WeierstrassCurve.CubicCharts
