/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNonzeroTorsion
/-! # Universal Weierstrass parameters with prime-level points -/

open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
  (W : WeierstrassCurve R) [W.IsElliptic]
/-- Nonzero torsion of invertible order greater than one covers every point of the base. -/
theorem nonzeroTorsionModel_surjective (n : ℕ) [NeZero n]
    (hn : IsUnit (n : R)) (hlarge : 1 < n) :
    Surjective (nonzeroTorsionModel W n).hom := by
  constructor
  intro x
  let K : Type u := IsLocalRing.ResidueField ((Spec (.of R)).presheaf.stalk x)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec (.of R)).fromSpecResidueField x)
  let : Algebra R K := φ.hom.toAlgebra
  let Ω := AlgebraicClosure K
  let : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  have hc : 0 < Nat.card (pointSource (R := R) Ω ⟶ nonzeroTorsionModel W n) := by
    rw [nonzeroTorsionFieldPoints_card W n hn Ω]
    have : 1 < n ^ 2 := one_lt_pow₀ hlarge (by decide : (2 : ℕ) ≠ 0)
    omega
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hc).1
  let z : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  refine ⟨p.left z, ?_⟩
  change (p.left ≫ (nonzeroTorsionModel W n).hom) z = x
  rw [p.w]
  have he : (pointSource (R := R) Ω).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ (Spec (.of R)).fromSpecResidueField x := by
    rw [← hφ, ← Spec.map_comp]
    rfl
  rw [he]
  exact (Spec (.of R)).fromSpecResidueField_apply x _

instance coefficientFintype : Fintype Coeff := by
  classical
  exact ⟨{.A₁, .A₂, .A₃, .A₄, .A₆}, by intro a; cases a <;> simp⟩

/-- The coefficient ring of Weierstrass equations with discriminant and level inverted. -/
abbrev LevelBase (n : ℕ) :=
  Localization.Away ((n : MvPolynomial Coeff ℤ) * Universal.curve.Δ)

instance levelBaseDomain (n : ℕ) [NeZero n] : IsDomain (LevelBase n) :=
  Localization.Away.isDomain
    (mul_ne_zero (by exact_mod_cast NeZero.ne n) Universal.Δ_curve_ne_zero)

/-- The universal elliptic Weierstrass equation over the level coefficient ring. -/
def levelCurve (n : ℕ) : WeierstrassCurve (LevelBase n) :=
  Universal.curve.map (algebraMap (MvPolynomial Coeff ℤ) (LevelBase n))

/-- Both the level and the discriminant are units in the parameter ring. -/
theorem levelBase_units (n : ℕ) :
    IsUnit (n : LevelBase n) ∧ IsUnit (levelCurve n).Δ := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := LevelBase n) ((n : MvPolynomial Coeff ℤ) * Universal.curve.Δ)
  rw [map_mul, (Commute.all _ _).isUnit_mul_iff] at h
  simpa only [levelCurve, WeierstrassCurve.map_Δ, map_natCast] using h

instance levelCurveElliptic (n : ℕ) : (levelCurve n).IsElliptic :=
  ⟨(levelBase_units n).2⟩

/-- An elliptic equation with invertible level determines its coefficient specialization. -/
def levelSpecialize {S : Type*} [CommRing S] (E : WeierstrassCurve S) [E.IsElliptic]
    (n : ℕ) (hn : IsUnit (n : S)) : LevelBase n →+* S :=
  IsLocalization.Away.lift ((n : MvPolynomial Coeff ℤ) * Universal.curve.Δ)
    (show IsUnit (E.specialize ((n : MvPolynomial Coeff ℤ) * Universal.curve.Δ)) by
      have he : WeierstrassCurve.map Universal.curve E.specialize = E := E.map_specialize
      rw [map_mul, map_natCast, ← WeierstrassCurve.map_Δ, he]
      exact hn.mul E.isUnit_Δ)

/-- Specializing the universal elliptic equation recovers the given equation. -/
theorem levelCurve_specialize {S : Type*} [CommRing S]
    (E : WeierstrassCurve S) [E.IsElliptic] (n : ℕ) (hn : IsUnit (n : S)) :
    (levelCurve n).map (levelSpecialize E n hn) = E := by
  rw [levelCurve, WeierstrassCurve.map_map, levelSpecialize,
    IsLocalization.Away.lift_comp]
  exact E.map_specialize

/-- The actual universal parameter scheme for an equation and a nonzero torsion point. -/
abbrev universalNonzeroTorsion (n : ℕ) [NeZero n] :
    Over (Spec (.of (LevelBase n))) :=
  nonzeroTorsionModel (levelCurve n) n

/-- The universal nonzero torsion parameter scheme is finite over the coefficient space. -/
theorem universalNonzeroTorsion_finite (n : ℕ) [NeZero n] :
    IsFinite (universalNonzeroTorsion n).hom :=
  nonzeroTorsionModel_finite _ n (levelBase_units n).1

/-- The universal nonzero torsion parameter scheme is étale over the coefficient space. -/
theorem universalNonzeroTorsion_etale (n : ℕ) [NeZero n] :
    Etale (universalNonzeroTorsion n).hom :=
  nonzeroTorsionModel_etale _ n (levelBase_units n).1

/-- For level greater than one the universal parameter map is surjective. -/
theorem universalNonzeroTorsion_surjective (n : ℕ) [NeZero n] (hn : 1 < n) :
    Surjective (universalNonzeroTorsion n).hom :=
  nonzeroTorsionModel_surjective _ n (levelBase_units n).1 hn


/-- The coefficient specialization recovers every map from the parameter ring. -/
theorem levelSpecialize_curveMap {S : Type*} [CommRing S] (n : ℕ)
    (f : LevelBase n →+* S) :
    levelSpecialize ((levelCurve n).map f) n
      (by simpa using (levelBase_units n).1.map f) = f := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers ((n : MvPolynomial Coeff ℤ) * Universal.curve.Δ))
  rw [levelSpecialize, IsLocalization.Away.lift_comp]
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · intro i
    cases i <;> simp [WeierstrassCurve.specialize, levelCurve,
      Universal.curve, WeierstrassCurve.map]

/-- The coefficient ring represents elliptic Weierstrass equations with invertible level. -/
def levelParameterEquiv (n : ℕ) (S : Type*) [CommRing S] :
    (LevelBase n →+* S) ≃
      {E : WeierstrassCurve S // IsUnit E.Δ ∧ IsUnit (n : S)} where
  toFun f := ⟨(levelCurve n).map f,
    ⟨((levelCurve n).map f).isUnit_Δ,
      by simpa using (levelBase_units n).1.map f⟩⟩
  invFun E := by
    have : E.val.IsElliptic := ⟨E.property.1⟩
    exact levelSpecialize E.val n E.property.2
  left_inv f := levelSpecialize_curveMap n f
  right_inv E := by
    have : E.val.IsElliptic := ⟨E.property.1⟩
    exact Subtype.ext (levelCurve_specialize E.val n E.property.2)

/-- Over a chosen elliptic equation, the universal prime-level fiber
represents exact-order points. -/
def universalPrimeLevelFieldPointEquiv (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic]
    (hp : IsUnit (p : K)) :
    (letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra;
      pointSource (R := LevelBase p) K ⟶ universalNonzeroTorsion p) ≃
      {P : E.toAffine.Point // addOrderOf P = p} := by
  letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra
  let e := primeTorsionClassicalEquiv (levelCurve p) p (levelBase_units p).1 K
  exact e.trans (Equiv.cast (congrArg
    (fun C : WeierstrassCurve K => {P : C.toAffine.Point // addOrderOf P = p})
      (levelCurve_specialize E p hp)))

end WeierstrassCurve.CubicCharts
