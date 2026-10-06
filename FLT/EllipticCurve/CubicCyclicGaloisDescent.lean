/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicNaturality
public import Mathlib.FieldTheory.Galois.Infinite

/-! # Galois descent of prime cyclic parameters

Rational points of the actual affine scalar quotient classify geometric
subgroups of prime order stable under Galois. A rational generator is not
required. Descent takes place on the invariant coordinate algebra.
-/
open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]
variable {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]
  [Algebra K L] [IsScalarTower R K L] [IsGalois K L]

/-- Galois-fixed algebra points descend at the level of their coordinates. -/
theorem algPoint_galois_descent (A : Type u) [CommRing A] [Algebra R A]
    (f : A →ₐ[R] L) (hf : ∀ σ : L ≃ₐ[K] L, ∀ a, σ (f a) = f a) :
    ∃ g : A →ₐ[R] K, (IsScalarTower.toAlgHom R K L).comp g = f := by
  let i := IsScalarTower.toAlgHom R K L
  let e := AlgEquiv.ofInjective i (algebraMap K L).injective
  have hr : ∀ a, f a ∈ i.range := by
    intro a
    exact (InfiniteGalois.mem_range_algebraMap_iff_fixed (f a)).mpr (fun σ => hf σ a)
  let h := f.codRestrict i.range hr
  refine ⟨e.symm.toAlgHom.comp h, ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (h a))

variable [IsNoetherianRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

omit [Algebra K L] [IsScalarTower R K L] [IsGalois K L] in
/-- Algebra points of the invariant ring are points of the scalar quotient. -/
def scalarQuotientCoordinatePointEquiv :
    (TorsionScalarInvariantRing W n →ₐ[R] K) ≃
      (pointSource K ⟶ scalarQuotientModel W n) :=
  specAlgPointEquiv (TorsionScalarInvariantRing W n) K

omit [Algebra K L] [IsScalarTower R K L] [IsGalois K L] in
/-- The invariant coordinate comparison commutes with extension of fields. -/
theorem scalarQuotientCoordinatePoint_map (f : K →ₐ[R] L)
    (q : TorsionScalarInvariantRing W n →ₐ[R] K) :
    scalarQuotientCoordinatePointEquiv (K := L) W n (f.comp q) =
      pointSourceMap f ≫ scalarQuotientCoordinatePointEquiv W n q := by
  apply Over.OverMorphism.ext
  exact Spec.map_comp (CommRingCat.ofHom q.toRingHom) (CommRingCat.ofHom f.toRingHom)

/-- Galois-fixed geometric parameters descend to the field of definition. -/
theorem scalarQuotientPoint_galois_descent
    (q : pointSource L ⟶ scalarQuotientModel W n)
    (hq : ∀ σ : L ≃ₐ[K] L, pointSourceMap (σ.restrictScalars R).toAlgHom ≫ q = q) :
    ∃ r : pointSource K ⟶ scalarQuotientModel W n,
      pointSourceMap (IsScalarTower.toAlgHom R K L) ≫ r = q := by
  obtain ⟨f, rfl⟩ := (scalarQuotientCoordinatePointEquiv (K := L) W n).surjective q
  have hf : ∀ σ : L ≃ₐ[K] L, ∀ a, σ (f a) = f a := by
    intro σ a
    have h := hq σ
    rw [← scalarQuotientCoordinatePoint_map] at h
    exact AlgHom.congr_fun ((scalarQuotientCoordinatePointEquiv W n).injective h) a
  obtain ⟨g, hg⟩ := algPoint_galois_descent _ f hf
  refine ⟨scalarQuotientCoordinatePointEquiv W n g, ?_⟩
  rw [← scalarQuotientCoordinatePoint_map, hg]


omit [Algebra K L] [IsScalarTower R K L] [IsGalois K L] in
/-- Extension of the coefficient field is injective on affine quotient points. -/
theorem scalarQuotientPoint_baseChange_injective (f : K →ₐ[R] L) :
    Function.Injective (fun q : pointSource K ⟶ scalarQuotientModel W n =>
      pointSourceMap f ≫ q) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (scalarQuotientCoordinatePointEquiv W n).surjective x
  obtain ⟨b, rfl⟩ := (scalarQuotientCoordinatePointEquiv W n).surjective y
  dsimp only at h
  rw [← scalarQuotientCoordinatePoint_map, ← scalarQuotientCoordinatePoint_map] at h
  apply congrArg (scalarQuotientCoordinatePointEquiv W n)
  ext c
  apply f.injective
  exact AlgHom.congr_fun ((scalarQuotientCoordinatePointEquiv W n).injective h) c

variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]
variable [IsAlgClosed L] [DecidableEq L]

/-- Geometric prime-order subgroups stable under every automorphism of the extension. -/
abbrev RationalPrimeSubgroups :=
  {H : AddSubgroup (W.map (algebraMap R L)).toAffine.Point //
    Nat.card H = p ∧ ∀ σ : L ≃ₐ[K] L,
      H.map (Affine.Point.map (W' := W.toAffine) (σ.restrictScalars R).toAlgHom) = H}

/-- The Galois-stable geometric subgroup attached to a rational parameter. -/
def rationalScalarSubgroupMap (x : pointSource K ⟶ scalarQuotientModel W p) :
    RationalPrimeSubgroups (K := K) (L := L) W p :=
  ⟨(scalarQuotientPrimeSubgroupEquiv W p L
      (pointSourceMap (IsScalarTower.toAlgHom R K L) ≫ x)).val,
    (scalarQuotientPrimeSubgroupEquiv W p L
      (pointSourceMap (IsScalarTower.toAlgHom R K L) ≫ x)).property,
    rationalScalarQuotient_subgroup_galoisStable W p x⟩

omit [IsGalois K L] in
/-- A rational parameter is determined by its geometric subgroup. -/
theorem rationalScalarSubgroupMap_injective :
    Function.Injective (rationalScalarSubgroupMap (K := K) (L := L) W p) := by
  intro x y h
  apply scalarQuotientPoint_baseChange_injective W p (IsScalarTower.toAlgHom R K L)
  apply (scalarQuotientPrimeSubgroupEquiv W p L).injective
  have hv := congrArg (fun z : RationalPrimeSubgroups (K := K) (L := L) W p => z.val) h
  exact Subtype.ext hv

/-- Every Galois-stable prime subgroup descends to a rational parameter. -/
theorem rationalScalarSubgroupMap_surjective :
    Function.Surjective (rationalScalarSubgroupMap (K := K) (L := L) W p) := by
  rintro ⟨H, hH, hstable⟩
  let q := (scalarQuotientPrimeSubgroupEquiv W p L).symm ⟨H, hH⟩
  have hq : ∀ σ : L ≃ₐ[K] L,
      pointSourceMap (σ.restrictScalars R).toAlgHom ≫ q = q := by
    intro σ
    apply (scalarQuotientPrimeSubgroupEquiv W p L).injective
    apply Subtype.ext
    rw [scalarQuotientPrimeSubgroupEquiv_map]
    change (scalarQuotientPrimeSubgroupEquiv W p L q).val.map _ =
      (scalarQuotientPrimeSubgroupEquiv W p L q).val
    simp only [q, Equiv.apply_symm_apply]
    exact hstable σ
  obtain ⟨r, hr⟩ := scalarQuotientPoint_galois_descent W p q hq
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change (scalarQuotientPrimeSubgroupEquiv W p L
    (pointSourceMap (IsScalarTower.toAlgHom R K L) ≫ r)).val = H
  rw [hr]
  exact congrArg Subtype.val ((scalarQuotientPrimeSubgroupEquiv W p L).apply_symm_apply _)

/-- Rational scalar quotient points classify Galois-stable geometric prime subgroups. -/
def rationalScalarQuotientSubgroupEquiv :
    (pointSource K ⟶ scalarQuotientModel W p) ≃
      RationalPrimeSubgroups (K := K) (L := L) W p :=
  Equiv.ofBijective (rationalScalarSubgroupMap W p)
    ⟨rationalScalarSubgroupMap_injective W p, rationalScalarSubgroupMap_surjective W p⟩

end WeierstrassCurve.CubicCharts
