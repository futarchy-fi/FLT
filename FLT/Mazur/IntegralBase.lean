/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPoints
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Canonical maps from the integral base

The base in Mazur, *Modular curves and the Eisenstein ideal* (1977), III §5,
p. 159, is `Spec ℤ[1/(2p)]`. Its generic and residue maps below are induced
by the universal property of localization. The residue construction requires
that `2p` be a unit; for prime `p` and `q` this is exactly `q ≠ 2` and `q ≠ p`.

Restrictions of sections use the over-category operations in `OverPoints`.
Thus each restricted point retains its specified morphism to the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur

/-- The ring of integers with `2p` inverted. -/
abbrev BaseRing (p : ℕ) := Localization.Away (2 * (p : ℤ))

/-- The integral base for the section diagram. -/
abbrev Base (p : ℕ) := Spec (CommRingCat.of (BaseRing p))

namespace IntegralBase

variable {p q : ℕ}

/-- The canonical map to a ring in which `2p` is invertible. -/
def lift {R : Type*} [CommRing R]
    (h : IsUnit (algebraMap ℤ R (2 * (p : ℤ)))) : BaseRing p →+* R :=
  IsLocalization.Away.lift (2 * (p : ℤ)) h

/-- The localization map agrees with the integer structure map. -/
theorem lift_algebraMap {R : Type*} [CommRing R]
    (h : IsUnit (algebraMap ℤ R (2 * (p : ℤ)))) (n : ℤ) :
    lift h (algebraMap ℤ (BaseRing p) n) = algebraMap ℤ R n :=
  IsLocalization.Away.lift_eq _ h n

/-- Maps from this localization are unique, since maps from the integers are unique. -/
theorem hom_ext {R : Type*} [CommRing R] (f g : BaseRing p →+* R) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (2 * (p : ℤ))) (Subsingleton.elim _ _)

/-- Every ring map from the base forces the inverted integer to remain a unit. -/
theorem isUnit_of_map {R : Type*} [CommRing R] (f : BaseRing p →+* R) :
    IsUnit (algebraMap ℤ R (2 * (p : ℤ))) := by
  have h := (IsLocalization.Away.algebraMap_isUnit (S := BaseRing p)
    (2 * (p : ℤ))).map f
  change IsUnit ((f.comp (algebraMap ℤ (BaseRing p))) (2 * (p : ℤ))) at h
  rwa [Subsingleton.elim (f.comp (algebraMap ℤ (BaseRing p))) (algebraMap ℤ R)] at h

/-- The denominator is invertible over the rationals whenever `p` is nonzero. -/
theorem genericUnit (hp : p ≠ 0) : IsUnit (algebraMap ℤ ℚ (2 * (p : ℤ))) := by
  simpa using (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num)
    (Nat.cast_ne_zero.mpr hp)) : IsUnit (2 * (p : ℚ)))

/-- The canonical homomorphism to the generic field. -/
def genericMap (hp : p ≠ 0) : BaseRing p →+* ℚ := lift (genericUnit hp)

theorem genericMap_algebraMap (hp : p ≠ 0) (n : ℤ) :
    genericMap hp (algebraMap ℤ (BaseRing p) n) = (n : ℚ) :=
  lift_algebraMap _ n

theorem genericMap_unique (hp : p ≠ 0) (f : BaseRing p →+* ℚ) :
    f = genericMap hp := hom_ext _ _

/-- Exactly the primes excluded from the base fail the required unit condition. -/
theorem residueUnit_iff (hp : p.Prime) (hq : q.Prime) :
    IsUnit (algebraMap ℤ (ZMod q) (2 * (p : ℤ))) ↔ q ≠ 2 ∧ q ≠ p := by
  change IsUnit ((2 * (p : ℤ) : ℤ) : ZMod q) ↔ _
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, IsUnit.mul_iff]
  rw [show (2 : ZMod q) = ((2 : ℕ) : ZMod q) from rfl,
    ZMod.isUnit_prime_iff_not_dvd Nat.prime_two, ZMod.isUnit_prime_iff_not_dvd hp,
    hq.dvd_iff_eq (by decide), hq.dvd_iff_eq hp.ne_one]

/-- Invertibility at an allowed residue prime. -/
theorem residueUnit (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    IsUnit (algebraMap ℤ (ZMod q) (2 * (p : ℤ))) :=
  (residueUnit_iff hp hq).mpr ⟨hq2, hqp⟩

/-- The canonical homomorphism to an allowed residue field. -/
def residueMap (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    BaseRing p →+* ZMod q := lift (residueUnit hp hq hq2 hqp)

theorem residueMap_algebraMap (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (n : ℤ) :
    residueMap hp hq hq2 hqp (algebraMap ℤ (BaseRing p) n) = (n : ZMod q) :=
  lift_algebraMap _ n

theorem residueMap_unique (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (f : BaseRing p →+* ZMod q) : f = residueMap hp hq hq2 hqp := hom_ext _ _

/-- A map to a prime residue field exists exactly at the allowed primes. -/
theorem residueMap_exists_iff (hp : p.Prime) (hq : q.Prime) :
    Nonempty (BaseRing p →+* ZMod q) ↔ q ≠ 2 ∧ q ≠ p := by
  constructor
  · rintro ⟨f⟩
    exact (residueUnit_iff hp hq).mp (isUnit_of_map f)
  · rintro ⟨hq2, hqp⟩
    exact ⟨residueMap hp hq hq2 hqp⟩

/-- The unit requirement rules out residue characteristic two. -/
theorem not_residueUnit_two (hp : p.Prime) :
    ¬ IsUnit (algebraMap ℤ (ZMod 2) (2 * (p : ℤ))) := by
  rw [residueUnit_iff hp Nat.prime_two]
  simp

/-- The unit requirement also rules out residue characteristic `p`. -/
theorem not_residueUnit_self (hp : p.Prime) :
    ¬ IsUnit (algebraMap ℤ (ZMod p) (2 * (p : ℤ))) := by
  rw [residueUnit_iff hp hp]
  simp

/-- No alternative choice of ring homomorphism can give reduction at two. -/
theorem no_residueMap_two (hp : p.Prime) : ¬ Nonempty (BaseRing p →+* ZMod 2) := by
  simp [residueMap_exists_iff hp Nat.prime_two]

/-- No alternative choice of ring homomorphism can give reduction at `p`. -/
theorem no_residueMap_self (hp : p.Prime) : ¬ Nonempty (BaseRing p →+* ZMod p) := by
  simp [residueMap_exists_iff hp hp]

/-- The specified generic morphism to the integral base. -/
def generic (hp : p ≠ 0) : Spec (CommRingCat.of ℚ) ⟶ Base p :=
  Spec.map (CommRingCat.ofHom (genericMap hp))

/-- The specified residue morphism to the integral base. -/
def residue (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    Spec (CommRingCat.of (ZMod q)) ⟶ Base p :=
  Spec.map (CommRingCat.ofHom (residueMap hp hq hq2 hqp))

/-- The generic morphism agrees with the usual morphism to `Spec ℤ`. -/
theorem generic_over_int (hp : p ≠ 0) :
    generic hp ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (BaseRing p))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) := by
  rw [generic, ← Spec.map_comp]
  congr 1
  ext n
  exact genericMap_algebraMap hp n

/-- The residue morphism agrees with the usual morphism to `Spec ℤ`. -/
theorem residue_over_int (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    residue hp hq hq2 hqp ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (BaseRing p))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod q))) := by
  rw [residue, ← Spec.map_comp]
  congr 1
  ext n
  exact residueMap_algebraMap hp hq hq2 hqp n

variable {X Y : Over (Base p)}

/-- Restrict an integral section to its canonical rational point. -/
def genericSection (hp : p ≠ 0) (x : Sections X) : Points X (generic hp) :=
  Sections.restrict (generic hp) x

/-- Restrict an integral section to its canonical residue point. -/
def residueSection (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (x : Sections X) : Points X (residue hp hq hq2 hqp) :=
  Sections.restrict (residue hp hq hq2 hqp) x

@[simp]
theorem genericSection_left (hp : p ≠ 0) (x : Sections X) :
    (genericSection hp x).left = generic hp ≫ x.left := rfl

@[simp]
theorem residueSection_left (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (x : Sections X) : (residueSection hp hq hq2 hqp x).left =
      residue hp hq hq2 hqp ≫ x.left := rfl

/-- The rational point retains its canonical structure map. -/
theorem genericSection_left_hom (hp : p ≠ 0) (x : Sections X) :
    (genericSection hp x).left ≫ X.hom = generic hp :=
  Sections.restrict_left_hom _ x

/-- The residue point retains its canonical structure map. -/
theorem residueSection_left_hom (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (x : Sections X) :
    (residueSection hp hq hq2 hqp x).left ≫ X.hom = residue hp hq hq2 hqp :=
  Sections.restrict_left_hom _ x

/-- The generic section diagram commutes in the over category. -/
@[simp]
theorem genericSection_map (hp : p ≠ 0) (f : X ⟶ Y) (x : Sections X) :
    genericSection hp (Sections.map f x) = Points.map f (genericSection hp x) :=
  Sections.restrict_map _ f x

/-- The residue section diagram commutes in the over category. -/
@[simp]
theorem residueSection_map (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (f : X ⟶ Y) (x : Sections X) :
    residueSection hp hq hq2 hqp (Sections.map f x) =
      Points.map f (residueSection hp hq hq2 hqp x) :=
  Sections.restrict_map _ f x

/-- Reduction at three is available throughout the final arithmetic range. -/
def residueThreeMap (hp : p.Prime) (hp17 : 17 ≤ p) : BaseRing p →+* ZMod 3 :=
  residueMap hp (by decide) (by decide) (by omega)

/-- The canonical map of spectra at three, ready for the two-cusp argument. -/
def residueThree (hp : p.Prime) (hp17 : 17 ≤ p) :
    Spec (CommRingCat.of (ZMod 3)) ⟶ Base p :=
  residue hp (by decide) (by decide) (by omega)

/-- The corresponding restriction of any integral section at three. -/
def residueThreeSection (hp : p.Prime) (hp17 : 17 ≤ p) (x : Sections X) :
    Points X (residueThree hp hp17) :=
  Sections.restrict (residueThree hp hp17) x

end IntegralBase

end FLT.Mazur
