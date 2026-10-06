/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionFlat
public import FLT.EllipticCurve.CubicTorsionNaturality
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
/-! # The finite étale parameter scheme of nonzero torsion points -/

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
  (W : WeierstrassCurve R) [W.IsElliptic]

/-- The zero section of the represented torsion group. -/
def torsionZeroSection (n : ℕ) : Spec (.of R) ⟶ (torsionModel W n).left :=
  (η[torsionModel W n]).left

/-- The zero section is a section of the torsion structure morphism. -/
@[simp] theorem torsionZeroSection_toBase (n : ℕ) :
    torsionZeroSection W n ≫ (torsionModel W n).hom = 𝟙 _ :=
  (η[torsionModel W n]).w

instance torsionZeroSectionClosedImmersion (n : ℕ) [NeZero n] :
    IsClosedImmersion (torsionZeroSection W n) := by
  have : IsClosedImmersion (torsionZeroSection W n ≫ (torsionModel W n).hom) := by
    rw [torsionZeroSection_toBase]
    infer_instance
  exact IsClosedImmersion.of_comp _ (torsionModel W n).hom

/-- The zero section of invertible-order torsion is an open immersion. -/
theorem torsionZeroSection_open (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    IsOpenImmersion (torsionZeroSection W n) := by
  have := torsionModel_etale W n hn
  have : Etale (torsionZeroSection W n ≫ (torsionModel W n).hom) := by
    rw [torsionZeroSection_toBase]
    infer_instance
  have : Etale (torsionZeroSection W n) := Etale.of_comp _ (torsionModel W n).hom
  exact IsOpenImmersion.of_flat_of_mono _

/-- The complement of the zero section in the actual torsion scheme. -/
def nonzeroTorsionOpen (n : ℕ) [NeZero n] : (torsionModel W n).left.Opens :=
  ⟨(Set.range (torsionZeroSection W n))ᶜ,
    (torsionZeroSection W n).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The scheme parametrizing fiberwise nonzero torsion points. -/
def nonzeroTorsionModel (n : ℕ) [NeZero n] : Over (Spec (.of R)) :=
  Over.mk ((nonzeroTorsionOpen W n).ι ≫ (torsionModel W n).hom)

/-- The nonzero locus is also closed when the torsion order is invertible. -/
theorem nonzeroTorsionOpen_closed (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    IsClosedImmersion (nonzeroTorsionOpen W n).ι := by
  have := torsionZeroSection_open W n hn
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (torsionZeroSection W n).isOpenMap.isOpen_range.isClosed_compl

/-- The nonzero torsion parameter scheme is finite over the base. -/
theorem nonzeroTorsionModel_finite (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    IsFinite (nonzeroTorsionModel W n).hom := by
  have := nonzeroTorsionOpen_closed W n hn
  change IsFinite ((nonzeroTorsionOpen W n).ι ≫ (torsionModel W n).hom)
  infer_instance

/-- The nonzero torsion parameter scheme is étale over the base. -/
theorem nonzeroTorsionModel_etale (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    Etale (nonzeroTorsionModel W n).hom := by
  have := torsionModel_etale W n hn
  change Etale ((nonzeroTorsionOpen W n).ι ≫ (torsionModel W n).hom)
  infer_instance

/-- The canonical inclusion of nonzero torsion into all torsion. -/
def nonzeroTorsionInclusion (n : ℕ) [NeZero n] :
    nonzeroTorsionModel W n ⟶ torsionModel W n :=
  Over.homMk (nonzeroTorsionOpen W n).ι rfl

/-- Maps to the nonzero torsion scheme are precisely torsion maps avoiding the zero section. -/
def nonzeroTorsionPointEquiv (n : ℕ) [NeZero n] (X : Over (Spec (.of R))) :
    (X ⟶ nonzeroTorsionModel W n) ≃
      {p : X ⟶ torsionModel W n //
        Set.range p.left ⊆ (nonzeroTorsionOpen W n : Set (torsionModel W n).left)} where
  toFun p := ⟨p ≫ nonzeroTorsionInclusion W n, by
    rintro _ ⟨x, rfl⟩
    exact (p.left x).property⟩
  invFun p := Over.homMk (IsOpenImmersion.lift (nonzeroTorsionOpen W n).ι p.1.left
    (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨p.1.left x, p.2 ⟨x, rfl⟩⟩, rfl⟩)) (by
      change (IsOpenImmersion.lift _ _ _) ≫
        ((nonzeroTorsionOpen W n).ι ≫ (torsionModel W n).hom) = X.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact p.1.w)
  left_inv p := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (nonzeroTorsionOpen W n).ι).mp
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv p := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _


/-- Over a field, avoiding the zero section is equivalent to being a nonidentity point. -/
theorem fieldPoint_range_nonzero (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    (K : Type u) [Field K] [Algebra R K]
    (p : pointSource (R := R) K ⟶ torsionModel W n) :
    Set.range p.left ⊆ (nonzeroTorsionOpen W n : Set (torsionModel W n).left) ↔ p ≠ 1 := by
  classical
  have : Subsingleton (pointSource (R := R) K).left :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  constructor
  · intro hp he
    subst p
    let x : Spec (.of K) := Classical.choice inferInstance
    have hx := hp (Set.mem_range_self x)
    change (1 : pointSource K ⟶ torsionModel W n).left x ∉
      Set.range (torsionZeroSection W n) at hx
    exact hx ⟨(Spec.map (CommRingCat.ofHom (algebraMap R K))) x, rfl⟩
  · intro hp y hy
    rcases hy with ⟨x, rfl⟩
    change p.left x ∉ Set.range (torsionZeroSection W n)
    intro hx
    have := torsionZeroSection_open W n hn
    have hr : Set.range p.left ⊆ Set.range (torsionZeroSection W n) := by
      rintro _ ⟨z, rfl⟩
      simpa only [Subsingleton.elim z x] using hx
    let t := IsOpenImmersion.lift (torsionZeroSection W n) p.left hr
    have ht : t ≫ torsionZeroSection W n = p.left := IsOpenImmersion.lift_fac _ _ _
    have he : t = (pointSource (R := R) K).hom := by
      rw [← p.w, ← ht, Category.assoc, torsionZeroSection_toBase, Category.comp_id]
    apply hp
    apply Over.OverMorphism.ext
    change p.left = (pointSource (R := R) K).hom ≫ torsionZeroSection W n
    rw [← ht, he]

/-- Field-valued points of the nonzero locus are the nonidentity represented torsion points. -/
def nonzeroTorsionFieldPointEquiv (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    (K : Type u) [Field K] [Algebra R K] :
    (pointSource (R := R) K ⟶ nonzeroTorsionModel W n) ≃
      {p : pointSource (R := R) K ⟶ torsionModel W n // p ≠ 1} :=
  (nonzeroTorsionPointEquiv W n (pointSource K)).trans
    (Equiv.subtypeEquivRight (fieldPoint_range_nonzero W n hn K))

/-- The nonzero torsion scheme represents classical nonzero torsion over fields. -/
def nonzeroTorsionClassicalEquiv (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K] :
    (pointSource (R := R) K ⟶ nonzeroTorsionModel W n) ≃
      {P : (nsmulAddMonoidHom n :
        (W.map (algebraMap R K)).toAffine.Point →+
        (W.map (algebraMap R K)).toAffine.Point).ker // P ≠ 0} :=
  (nonzeroTorsionFieldPointEquiv W n hn K).trans
    ((classicalTorsionMulEquiv W K n).toEquiv.subtypeEquiv (by
      intro p
      exact not_congr ((map_eq_one_iff (classicalTorsionMulEquiv W K n)
        (classicalTorsionMulEquiv W K n).injective).symm)))


/-- At prime level, this parameter scheme represents classical points of exact prime order. -/
def primeTorsionClassicalEquiv (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp : IsUnit (p : R)) (K : Type u) [Field K] [Algebra R K] [DecidableEq K] :
    (pointSource (R := R) K ⟶ nonzeroTorsionModel W p) ≃
      {P : (W.map (algebraMap R K)).toAffine.Point // addOrderOf P = p} :=
  (nonzeroTorsionClassicalEquiv W p hp K).trans
    { toFun := fun P => ⟨P.1.val, addOrderOf_eq_prime P.1.property
        (fun h => P.2 (Subtype.ext h))⟩
      invFun := fun P => ⟨⟨P.val, (addOrderOf_eq_prime_iff.mp P.property).1⟩, by
        intro h
        exact (addOrderOf_eq_prime_iff.mp P.property).2 (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The nonzero torsion scheme has n² minus one points over a separably closed field. -/
theorem nonzeroTorsionFieldPoints_card (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    (K : Type u) [Field K] [Algebra R K] [IsSepClosed K] :
    Nat.card (pointSource (R := R) K ⟶ nonzeroTorsionModel W n) = n ^ 2 - 1 := by
  classical
  let T := (nsmulAddMonoidHom n :
    (W.map (algebraMap R K)).toAffine.Point →+
    (W.map (algebraMap R K)).toAffine.Point).ker
  have hc : Nat.card T = n ^ 2 :=
    (W.map (algebraMap R K)).card_torsion_of_divisionDifferentialDefect
      (by simpa using (hn.map (algebraMap R K)).ne_zero)
      ((W.map (algebraMap R K)).divisionDifferentialDefect_eq_zero n)
  have : Finite T := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero 2 (NeZero.ne n))
  let : Fintype T := Fintype.ofFinite T
  rw [Nat.card_congr (nonzeroTorsionClassicalEquiv W n hn K)]
  change Nat.card {P : T // P ≠ 0} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc]

end WeierstrassCurve.CubicCharts
