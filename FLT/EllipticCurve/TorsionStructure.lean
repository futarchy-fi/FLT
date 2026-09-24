/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Recognizing powers of a finite cyclic group from torsion cardinalities

The proof inducts on the desired rank. The cardinality assumptions force the exponent to be
`n`, so there is an element of order `n`. Its cyclic subgroup splits off: extend its character
to the divisible group `ℝ / ℤ`, then restrict the extended character to `n`-torsion. The kernel
has the same torsion cardinality formula with rank reduced by one.
-/

@[expose] public section

namespace TorsionCardinality

/-- An additive equivalence restricts to an equivalence on integer torsion. -/
def congr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (d : ℕ) :
    Submodule.torsionBy ℤ A d ≃+ Submodule.torsionBy ℤ B d where
  toFun x := ⟨e x, by
    change (d : ℤ) • e x.val = 0
    rw [← map_zsmul, (show (d : ℤ) • x.val = 0 from x.property), map_zero]⟩
  invFun x := ⟨e.symm x, by
    change (d : ℤ) • e.symm x.val = 0
    rw [← map_zsmul, (show (d : ℤ) • x.val = 0 from x.property), map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add e x.val y.val)

/-- Torsion in a product is the product of the torsion subgroups. -/
def prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] (d : ℕ) :
    Submodule.torsionBy ℤ (A × B) d ≃+
      Submodule.torsionBy ℤ A d × Submodule.torsionBy ℤ B d where
  toFun x := (⟨x.val.1, congrArg Prod.fst x.property⟩,
    ⟨x.val.2, congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- A cyclic group of order `n` has exactly `d` elements killed by each divisor `d` of `n`. -/
theorem card_zmod {n : ℕ} (hn : 0 < n) {d : ℕ} (hd : d ∣ n) :
    Nat.card (Submodule.torsionBy ℤ (ZMod n) d) = d := by
  let : NeZero n := ⟨hn.ne'⟩
  let e : Submodule.torsionBy ℤ (ZMod n) d ≃
      (nsmulAddMonoidHom (α := ZMod n) d).ker :=
    { toFun := fun x => ⟨x.val, by
        change d • x.val = 0
        simpa only [natCast_zsmul] using
          (show (d : ℤ) • x.val = 0 from x.property)⟩
      invFun := fun x => ⟨x.val, by
        change (d : ℤ) • x.val = 0
        exact_mod_cast (show d • x.val = 0 from x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, IsAddCyclic.card_nsmulAddMonoidHom_ker]
  simpa using Nat.gcd_eq_right hd

/-- The canonical embedding into the circle identifies `ZMod n` with its `n`-torsion. -/
noncomputable def circleTorsionEquiv (n : ℕ) [NeZero n] :
    ZMod n ≃+ Submodule.torsionBy ℤ UnitAddCircle n := by
  let j : ZMod n →+ Submodule.torsionBy ℤ UnitAddCircle n :=
    { toFun := fun x => ⟨ZMod.toAddCircle x, by
        change (n : ℤ) • ZMod.toAddCircle x = 0
        rw [← map_zsmul]
        simp⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hj : Function.Injective j := fun x y h =>
    ZMod.toAddCircle_injective n (congrArg Subtype.val h)
  let e : Submodule.torsionBy ℤ UnitAddCircle n ≃
      {x : UnitAddCircle | n • x = 0} :=
    { toFun := fun x => ⟨x.val, by
        change n • x.val = 0
        simpa only [natCast_zsmul] using
          (show (n : ℤ) • x.val = 0 from x.property)⟩
      invFun := fun x => ⟨x.val, by
        change (n : ℤ) • x.val = 0
        simpa only [natCast_zsmul] using (show n • x.val = 0 from x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hb := AddCircle.card_torsion_le_of_isSMulRegular (1 : ℝ) n (NeZero.ne n)
    (by
      intro x y h
      simpa only [nsmul_eq_mul, mul_right_inj' (Nat.cast_ne_zero.mpr (NeZero.ne n))] using h)
  obtain ⟨hf, hc⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hb
  letI : Finite {x : UnitAddCircle | n • x = 0} := hf.to_subtype
  letI : Finite (Submodule.torsionBy ℤ UnitAddCircle n) := Finite.of_equiv _ e.symm
  apply AddEquiv.ofBijective j
  apply hj.bijective_of_nat_card_le
  rw [Nat.card_congr e, Nat.card_eq_fintype_card (α := ZMod n), ZMod.card]
  exact hc

/-- A copy of `ZMod n` in a group annihilated by `n` admits a retraction. -/
theorem exists_retraction {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n)
    (hA : ∀ x : A, n • x = 0) (i : ZMod n →+ A) (hi : Function.Injective i) :
    ∃ f : A →+ ZMod n, f.comp i = AddMonoidHom.id _ := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    i hi ZMod.toAddCircle
  let f' : A →+ Submodule.torsionBy ℤ UnitAddCircle n :=
    { toFun := fun x => ⟨f x, by
        change (n : ℤ) • f x = 0
        simpa only [natCast_zsmul, ← map_nsmul, map_zero] using congrArg f (hA x)⟩
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun x y => Subtype.ext (map_add f x y) }
  refine ⟨(circleTorsionEquiv n).symm.toAddMonoidHom.comp f', ?_⟩
  ext x
  apply (circleTorsionEquiv n).injective
  change (circleTorsionEquiv n) ((circleTorsionEquiv n).symm (f' (i x))) =
    (circleTorsionEquiv n) x
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  exact DFunLike.congr_fun hf x

/-- If every element is killed by `d`, its torsion subgroup is the entire group. -/
def whole {A : Type*} [AddCommGroup A] (d : ℕ) (hA : ∀ x : A, d • x = 0) :
    Submodule.torsionBy ℤ A d ≃+ A where
  toFun x := x.val
  invFun x := ⟨x, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hA x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- A retraction onto a cyclic subgroup gives a product decomposition. -/
def split {A : Type*} [AddCommGroup A] {n : ℕ}
    (i : ZMod n →+ A) (f : A →+ ZMod n) (hf : f.comp i = AddMonoidHom.id _) :
    A ≃+ ZMod n × f.ker where
  toFun x := (f x, ⟨x - i (f x), by
    change f (x - i (f x)) = 0
    rw [map_sub, show f (i (f x)) = f x from DFunLike.congr_fun hf (f x), sub_self]⟩)
  invFun x := i x.1 + x.2.val
  left_inv x := by dsimp; abel
  right_inv x := by
    have hx : f x.2.val = 0 := x.2.property
    have hi : f (i x.1) = x.1 := DFunLike.congr_fun hf x.1
    apply Prod.ext
    · change f (i x.1 + x.2.val) = x.1
      rw [map_add, hi, hx, add_zero]
    · apply Subtype.ext
      change i x.1 + x.2.val - i (f (i x.1 + x.2.val)) = x.2.val
      rw [map_add, hi, hx, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add f x y
    · apply Subtype.ext
      change x + y - i (f (x + y)) = (x - i (f x)) + (y - i (f y))
      rw [map_add, map_add]
      abel

/-- Separate the first coordinate of a finite power of an additive group. -/
def finSucc (B : Type*) [AddCommGroup B] (r : ℕ) :
    B × (Fin r → B) ≃+ (Fin (r + 1) → B) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, fun j => x j.succ)
  left_inv x := by simp
  right_inv x := by ext j; exact Fin.cases rfl (fun _ => rfl) j
  map_add' x y := by ext j; exact Fin.cases rfl (fun _ => rfl) j

/-- Torsion cardinalities determine a finite group annihilated by `n` as a power of `ZMod n`. -/
theorem equiv_of_card {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (hA : ∀ x : A, n • x = 0)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty (A ≃+ (Fin r → ZMod n)) := by
  classical
  induction r generalizing A with
  | zero =>
    have hc : Nat.card A = 1 := by
      rw [← Nat.card_congr (whole n hA).toEquiv, h n dvd_rfl, pow_zero]
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hc).1
    exact ⟨AddEquiv.ofBijective (0 : A →+ (Fin 0 → ZMod n))
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩⟩
  | succ r ih =>
    have hc : Nat.card A = n ^ (r + 1) := by
      rw [← Nat.card_congr (whole n hA).toEquiv, h n dvd_rfl]
    have : Finite A := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ hn.ne')
    have he : AddMonoid.exponent A ∣ n :=
      AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hA
    have heA : ∀ x : A, AddMonoid.exponent A • x = 0 :=
      AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp dvd_rfl
    have heq : AddMonoid.exponent A = n := by
      apply Nat.pow_left_injective (Nat.succ_ne_zero r)
      change AddMonoid.exponent A ^ (r + 1) = n ^ (r + 1)
      rw [← h _ he, Nat.card_congr (whole _ heA).toEquiv, hc]
    obtain ⟨g, hg⟩ := AddMonoid.exists_addOrderOf_eq_exponent
      (AddMonoid.ExponentExists.of_finite (G := A))
    rw [heq] at hg
    let e : ZMod n ≃+ AddSubgroup.zmultiples g :=
      (ZMod.ringEquivCongr ((Nat.card_zmultiples g).trans hg)).symm.toAddEquiv.trans
        (zmodAddCyclicAddEquiv inferInstance)
    let i : ZMod n →+ A := (AddSubgroup.zmultiples g).subtype.comp e.toAddMonoidHom
    have hi : Function.Injective i := Subtype.val_injective.comp e.injective
    obtain ⟨f, hf⟩ := exists_retraction hn hA i hi
    let E := split i f hf
    have hK : ∀ x : f.ker, n • x = 0 := fun x => Subtype.ext (hA x.val)
    have hcard : ∀ d : ℕ, d ∣ n →
        Nat.card (Submodule.torsionBy ℤ f.ker d) = d ^ r := by
      intro d hd
      have hdpos := Nat.pos_of_dvd_of_pos hd hn
      apply Nat.eq_of_mul_eq_mul_left hdpos
      have ht := Nat.card_congr ((congr E d).trans (prod (ZMod n) f.ker d)).toEquiv
      rw [Nat.card_prod, card_zmod hn hd, h d hd, pow_succ, mul_comm] at ht
      exact ht.symm
    obtain ⟨eK⟩ := ih hK hcard
    exact ⟨E.trans (((AddEquiv.refl _).prodCongr eK).trans (finSucc _ r))⟩

/-- Taking `d`-torsion inside `n`-torsion changes nothing when `d` divides `n`. -/
def nested {A : Type*} [AddCommGroup A] {n d : ℕ} (hd : d ∣ n) :
    Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d ≃+
      Submodule.torsionBy ℤ A d where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, Submodule.torsionBy_le_torsionBy_of_dvd (d : ℤ) (n : ℤ)
    (by exact_mod_cast hd) x.property⟩, Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end TorsionCardinality
