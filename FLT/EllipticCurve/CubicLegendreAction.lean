/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreParameterSymmetries
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.RingTheory.Invariant.Basic

/-! # The six integral Legendre parameter symmetries

The involutions λ ↦ 1 − λ and λ ↦ λ⁻¹ define an action of the dihedral
group of order six over the j-line. The spectrum of the fixed subring
is finite and surjective over the j-line, and the map from the Legendre
chart to this spectrum is finite, surjective and invariant.
Prime ideals above the same invariant prime form a single orbit.

This is a quotient of the coefficient chart. It does not construct
the modular curve or descend the family of cyclic subgroups.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
open AlgebraicGeometry CategoryTheory
open scoped Pointwise
variable {G : Type*} [Group G]

/-- The six words determined by two involutions. -/
def dihedralThreeMap (a b : G) : DihedralGroup 3 → G
  | .r i => if i = 0 then 1 else if i = 1 then a * b else b * a
  | .sr i => if i = 0 then a else if i = 1 then b else a * b * a

/-- Two involutions satisfying the braid relation define a dihedral action. -/
def dihedralThreeHom (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) : DihedralGroup 3 →* G where
  toFun := dihedralThreeMap a b
  map_one' := by
    change dihedralThreeMap a b (.r 0) = 1
    simp (config := { decide := true }) only [dihedralThreeMap, ite_true]
  map_mul' := by
    have haa (x : G) : a * (a * x) = x := by rw [← mul_assoc, ha, one_mul]
    have hbb (x : G) : b * (b * x) = x := by rw [← mul_assoc, hb, one_mul]
    have hab' : a * (b * a) = b * (a * b) := by simpa only [mul_assoc] using hab
    have habx (x : G) : a * (b * (a * x)) = b * (a * (b * x)) := by
      simpa only [mul_assoc] using congrArg (fun z => z * x) hab
    have hz (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
      have hi := ZMod.val_lt i
      have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hv with hv | hv | hv
      · left
        rw [← ZMod.natCast_zmod_val i, hv, Nat.cast_zero]
      · right; left
        rw [← ZMod.natCast_zmod_val i, hv, Nat.cast_one]
      · right; right
        rw [← ZMod.natCast_zmod_val i, hv, Nat.cast_ofNat]
    rintro (i | i) (j | j) <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;>
      rcases hz i with rfl | rfl | rfl <;> rcases hz j with rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [dihedralThreeMap, ite_true, ite_false,
        mul_assoc, ha, hb, one_mul, mul_one, haa, hbb, hab', habx]

/-- Swapping zero and one is an involution over the j-line. -/
theorem legendreSwapParameterAlgEquiv_square (p : ℕ) [NeZero p] :
    legendreSwapParameterAlgEquiv p * legendreSwapParameterAlgEquiv p = 1 := by
  ext x
  exact legendreSwapParameterMap_involutive p x

/-- Taking the reciprocal is an involution over the j-line. -/
theorem legendreReciprocalParameterAlgEquiv_square (p : ℕ) [NeZero p] :
    legendreReciprocalParameterAlgEquiv p * legendreReciprocalParameterAlgEquiv p = 1 := by
  ext x
  exact legendreReciprocalParameterMap_involutive p x

/-- The two parameter involutions satisfy the braid relation. -/
theorem legendreParameterAlgEquiv_braid (p : ℕ) [NeZero p] :
    legendreSwapParameterAlgEquiv p * legendreReciprocalParameterAlgEquiv p *
        legendreSwapParameterAlgEquiv p =
      legendreReciprocalParameterAlgEquiv p * legendreSwapParameterAlgEquiv p *
        legendreReciprocalParameterAlgEquiv p := by
  ext x
  exact DFunLike.congr_fun (legendreParameterMaps_braid p) x

/-- The six integral Legendre symmetries, as automorphisms over the j-line. -/
def legendreParameterSymmetries (p : ℕ) [NeZero p] :
    DihedralGroup 3 →* (LegendreBase p ≃ₐ[LegendreJBase p] LegendreBase p) :=
  dihedralThreeHom (legendreSwapParameterAlgEquiv p) (legendreReciprocalParameterAlgEquiv p)
    (legendreSwapParameterAlgEquiv_square p) (legendreReciprocalParameterAlgEquiv_square p)
    (legendreParameterAlgEquiv_braid p)

instance legendreParameterAction (p : ℕ) [NeZero p] :
    MulSemiringAction (DihedralGroup 3) (LegendreBase p) :=
  MulSemiringAction.compHom _ (legendreParameterSymmetries p)

instance legendreParameterActionComm (p : ℕ) [NeZero p] :
    SMulCommClass (DihedralGroup 3) (LegendreJBase p) (LegendreBase p) where
  smul_comm g r x := (legendreParameterSymmetries p g).toLinearEquiv.map_smul r x

/-- The subring of Legendre coordinates fixed by all six parameter symmetries. -/
abbrev LegendreInvariantRing (p : ℕ) [NeZero p] :=
  FixedPoints.subring (LegendreBase p) (DihedralGroup 3)

instance legendreInvariantAlgebra (p : ℕ) [NeZero p] :
    Algebra (LegendreJBase p) (LegendreInvariantRing p) :=
  (RingHom.codRestrict (algebraMap (LegendreJBase p) (LegendreBase p))
    (LegendreInvariantRing p) (fun r g => smul_algebraMap g r)).toAlgebra

instance legendreInvariantModule (p : ℕ) [NeZero p] :
    Module (LegendreJBase p) (LegendreInvariantRing p) :=
  @Algebra.toModule _ _ _ _ (legendreInvariantAlgebra p)

instance legendreInvariantFaithful (p : ℕ) [NeZero p] :
    FaithfulSMul (LegendreInvariantRing p) (LegendreBase p) where
  eq_of_smul_eq_smul {a b} h := by
    apply Subtype.ext
    have hh := h 1
    change (a : LegendreBase p) * 1 = (b : LegendreBase p) * 1 at hh
    simpa only [mul_one] using hh

instance legendreInvariantTower (p : ℕ) [NeZero p] :
    IsScalarTower (LegendreJBase p) (LegendreInvariantRing p) (LegendreBase p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The invariant coordinates embed as an algebra over the j-line. -/
def legendreInvariantInclusion (p : ℕ) [NeZero p] :
    LegendreInvariantRing p →ₐ[LegendreJBase p] LegendreBase p where
  __ := (LegendreInvariantRing p).subtype
  commutes' _ := rfl

instance legendreJBaseNoetherian (p : ℕ) : IsNoetherianRing (LegendreJBase p) := by
  change IsNoetherianRing (Polynomial (LegendreConstants p))
  infer_instance

instance legendreInvariantFinite (p : ℕ) [NeZero p] :
    Module.Finite (LegendreJBase p) (LegendreInvariantRing p) := by
  have : Module.Finite (LegendreJBase p) (LegendreBase p) := legendreBaseFiniteOverJ p
  have : _root_.IsNoetherian (LegendreJBase p) (LegendreBase p) :=
    isNoetherian_of_isNoetherianRing_of_finite (LegendreJBase p) (LegendreBase p)
  exact Module.Finite.of_injective
    (legendreInvariantInclusion p).toLinearMap Subtype.val_injective

instance legendreFiniteOverInvariants (p : ℕ) [NeZero p] :
    Module.Finite (LegendreInvariantRing p) (LegendreBase p) :=
  Module.Finite.of_restrictScalars_finite (LegendreJBase p) _ _

/-- The affine quotient of the coefficient chart by its six parameter symmetries. -/
def legendreOrbitModel (p : ℕ) [NeZero p] : Over (Spec (.of (LegendreJBase p))) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (LegendreJBase p) (LegendreInvariantRing p))))

/-- The map from the Legendre chart to its invariant spectrum. -/
def legendreOrbitMap (p : ℕ) [NeZero p] :
    Spec (.of (LegendreBase p)) ⟶ (legendreOrbitModel p).left :=
  Spec.map (CommRingCat.ofHom (LegendreInvariantRing p).subtype)

instance legendreOrbitMapFinite (p : ℕ) [NeZero p] : IsFinite (legendreOrbitMap p) := by
  rw [legendreOrbitMap, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance legendreOrbitMapSurjective (p : ℕ) [NeZero p] : Surjective (legendreOrbitMap p) := by
  have : Algebra.IsIntegral (LegendreInvariantRing p) (LegendreBase p) :=
    Algebra.IsIntegral.of_finite _ _
  exact ⟨Algebra.IsIntegral.comap_surjective _ _⟩

instance legendreOrbitModelFinite (p : ℕ) [NeZero p] : IsFinite (legendreOrbitModel p).hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap (LegendreJBase p) (LegendreInvariantRing p))))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The invariant quotient factors the original Legendre map to the j-line. -/
theorem legendreOrbitMap_toJ (p : ℕ) [NeZero p] :
    legendreOrbitMap p ≫ (legendreOrbitModel p).hom = legendreToJ p := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

instance legendreInvariantExtension (p : ℕ) [NeZero p] :
    Algebra.IsInvariant (LegendreInvariantRing p) (LegendreBase p) (DihedralGroup 3) where
  isInvariant x hx := ⟨⟨x, hx⟩, rfl⟩

/-- Prime ideals with the same invariant contraction lie in a single orbit. -/
theorem legendreInvariantPrime_orbit (p : ℕ) [NeZero p]
    (P Q : Ideal (LegendreBase p)) [P.IsPrime] [Q.IsPrime]
    (h : P.under (LegendreInvariantRing p) = Q.under (LegendreInvariantRing p)) :
    ∃ g : DihedralGroup 3, Q = g • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq
    (LegendreInvariantRing p) (LegendreBase p) (DihedralGroup 3) P Q h

/-- The map to the invariant spectrum is unchanged by every parameter symmetry. -/
theorem legendreOrbitMap_invariant (p : ℕ) [NeZero p] (g : DihedralGroup 3) :
    Spec.map (CommRingCat.ofHom (legendreParameterSymmetries p g).toRingHom) ≫
      legendreOrbitMap p = legendreOrbitMap p := by
  rw [legendreOrbitMap, ← Spec.map_comp]
  congr 1
  ext x
  exact x.property g

instance legendreOrbitModelSurjective (p : ℕ) [NeZero p] :
    Surjective (legendreOrbitModel p).hom := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := (inferInstance : Surjective (legendreToJ p)).1 x
  refine ⟨legendreOrbitMap p y, ?_⟩
  change (legendreOrbitMap p ≫ (legendreOrbitModel p).hom) y = x
  rw [legendreOrbitMap_toJ]
  exact hy

end WeierstrassCurve.CubicCharts

