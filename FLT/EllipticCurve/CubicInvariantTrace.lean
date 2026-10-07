/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps
/-! # A trace retraction for free actions on field-valued points

Linear independence of distinct multiplicative characters makes the
orbit trace nonzero at every residue-field point. Integral lying-over
then shows that the invariant-valued trace is surjective. A trace-one
element gives a linear retraction of the invariant inclusion, proving
flatness and injectivity after arbitrary base change without dividing
by the group order.
-/

open scoped BigOperators
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u v

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- The orbit sum as a linear map to the invariant algebra. -/
def freeInvariantTrace : A →ₗ[FixedPoints.subalgebra R A G] FixedPoints.subalgebra R A G where
  toFun a := ⟨∑ g : G, g • a, by
    intro h
    rw [Finset.smul_sum]
    simp only [← mul_smul]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)⟩
  map_add' a b := by
    apply Subtype.ext
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' r a := by
    apply Subtype.ext
    change (∑ g : G, g • ((r : A) * a)) = (r : A) * ∑ g : G, g • a
    simp only [MulSemiringAction.smul_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [show g • (r : A) = (r : A) from r.property g]

/-- A sum of distinct multiplicative characters cannot vanish identically. -/
theorem sum_characters_ne_zero (K : Type u) [Field K] (f : A →+* K)
    (hf : Function.Injective (fun g : G => fun a : A => f (g • a))) :
    ∃ a : A, (∑ g : G, f (g • a)) ≠ 0 := by
  classical
  let χ : G → (A →* K) := fun g =>
    f.toMonoidHom.comp (MulSemiringAction.toRingHom G A g).toMonoidHom
  have hi : Function.Injective χ := by
    intro g h he
    exact hf (congrArg (fun q : A →* K => (q : A → K)) he)
  have hl := (linearIndependent_monoidHom A K).comp χ hi
  by_contra hn
  push Not at hn
  have hs : Fintype.linearCombination K (fun g => (χ g : A → K)) (fun _ => (1 : K)) = 0 := by
    ext a
    simpa [Fintype.linearCombination_apply, χ] using hn a
  have he := hl.fintypeLinearCombination_injective (hs.trans (map_zero _).symm)
  exact one_ne_zero (congrFun he (1 : G))

/-- A free action on all field-valued points has surjective invariant-valued trace. -/
theorem freeInvariantTrace_surjective
    (hfree : ∀ (K : Type u) [Field K] (f : A →+* K),
      Function.Injective (fun g : G => fun a : A => f (g • a))) :
    Function.Surjective (freeInvariantTrace R A G) := by
  classical
  let D := FixedPoints.subalgebra R A G
  let τ := freeInvariantTrace R A G
  apply LinearMap.range_eq_top.mp
  by_contra hn
  let I : Ideal D := τ.range
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hn
  let : m.IsMaximal := hm
  let : Algebra.IsInvariant D A G := ⟨fun a ha => ⟨⟨a, ha⟩, rfl⟩⟩
  have : Algebra.IsIntegral D A := Algebra.IsInvariant.isIntegral D A G
  obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective D A ⟨m, inferInstance⟩
  let K := q.asIdeal.ResidueField
  let f : A →+* K := algebraMap A K
  obtain ⟨a, ha⟩ := sum_characters_ne_zero A G K f (hfree K f)
  apply ha
  have ht : τ a ∈ m := hIm ⟨a, rfl⟩
  have hq' : Ideal.comap (algebraMap D A) q.asIdeal = m := congrArg PrimeSpectrum.asIdeal hq
  rw [← hq'] at ht
  have hz : f (τ a).val = 0 := Ideal.algebraMap_residueField_eq_zero.mpr ht
  change f (∑ g : G, g • a) = 0 at hz
  simpa only [map_sum] using hz

/-- A trace-weighted linear map from the algebra to its invariants. -/
def freeInvariantProjection (a : A) :
    A →ₗ[R] FixedPoints.subalgebra R A G :=
  ((freeInvariantTrace R A G).restrictScalars R).comp (LinearMap.mul R A a)

/-- A trace-one element makes the invariant inclusion a split linear injection. -/
theorem freeInvariantProjection_retract (a : A) (ha : freeInvariantTrace R A G a = 1) :
    (freeInvariantProjection R A G a).comp
      (FixedPoints.subalgebra R A G).val.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro d
  change freeInvariantTrace R A G (a * (d : A)) = d
  rw [mul_comm]
  change freeInvariantTrace R A G (d • a) = d
  rw [map_smul, ha, smul_eq_mul, mul_one]

omit [Fintype G] in
/-- Invariants of a flat algebra under a field-point-free action are flat. -/
theorem freeInvariant_flat [Finite G] [Module.Flat R A]
    (hfree : ∀ (K : Type u) [Field K] (f : A →+* K),
      Function.Injective (fun g : G => fun a : A => f (g • a))) :
    Module.Flat R (FixedPoints.subalgebra R A G) := by
  let := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := freeInvariantTrace_surjective R A G hfree 1
  exact Module.Flat.of_retract _ _ (freeInvariantProjection_retract R A G a ha)

open scoped TensorProduct in
omit [Fintype G] in
/-- The invariant inclusion of a field-point-free action stays injective after base change. -/
theorem freeInvariantTensor_injective [Finite G] (S : Type u) [CommRing S] [Algebra R S]
    (hfree : ∀ (K : Type u) [Field K] (f : A →+* K),
      Function.Injective (fun g : G => fun a : A => f (g • a))) :
    Function.Injective
      (Algebra.TensorProduct.lTensor S (FixedPoints.subalgebra R A G).val :
        S ⊗[R] FixedPoints.subalgebra R A G →ₐ[S] S ⊗[R] A) := by
  let := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := freeInvariantTrace_surjective R A G hfree 1
  let i := (FixedPoints.subalgebra R A G).val.toLinearMap
  let r := freeInvariantProjection R A G a
  have h : (LinearMap.lTensor S r).comp (LinearMap.lTensor S i) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, freeInvariantProjection_retract R A G a ha,
      LinearMap.lTensor_id]
  change Function.Injective (LinearMap.lTensor S i)
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun h x)

end WeierstrassCurve.CubicCharts
