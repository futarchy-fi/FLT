/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCoefficientSectionNaturality
public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveTangentCoordinates

/-!
# Original arithmetic specialization in the two complete polygon orientations

The coordinates are those of the actual coefficient restriction of the
original integral section. They are independent of the chosen root in the
first orientation, and intrinsic reflection gives the opposite orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "k" => ResidueField A
local notation "C" => coefficientShearRootStrictPositiveCoordinates
  hπ data D s hs hstart hk hp
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp
local notation "ρ" => coefficientShearRootStrictPositivePolygonReflectionIso
  hπ data D s hs hstart hk hp
local notation "Z" => (PolygonAtlas.polygon k (2 * s + 5)).left

/-- Full first-orientation polygon coordinates of the actual original arithmetic closed point. -/
def e0StrictPositivePolygonPoint (r : k) (P : ellipticE0 A W) : Spec (.of k) ⟶ Z :=
  e0CoefficientSection A hπ data k r (s + 1) hs P ≫ (C r).inv

/-- Full opposite-orientation coordinates of that same actual arithmetic point. -/
def e0StrictPositiveOppositePoint (r : k) (P : ellipticE0 A W) : Spec (.of k) ⟶ Z :=
  e0CoefficientSection A hπ data k r (s + 1) hs P ≫ (O r).inv

/-- Reconstruction recovers the actual original coefficient section on the whole model. -/
@[reassoc] theorem e0StrictPositivePolygonPoint_reconstruction (r : k) (P : ellipticE0 A W) :
    e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r P ≫ (C r).hom =
      e0CoefficientSection A hπ data k r (s + 1) hs P := by
  rw [e0StrictPositivePolygonPoint, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Changing the chosen coefficient root does not change the first arithmetic coordinates. -/
theorem e0StrictPositivePolygonPoint_root_independent (r t : k) (P : ellipticE0 A W) :
    e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r P =
      e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp t P := by
  apply (cancel_mono (C t).hom).mp
  rw [e0StrictPositivePolygonPoint_reconstruction,
    ← coefficientShearRootStrictPositiveCoordinates_rootChange hπ data D s hs hstart hk hp r t,
    e0StrictPositivePolygonPoint_reconstruction_assoc, e0CoefficientSection_rootChange]

/-- Actual arithmetic points change orientation by the original whole-polygon reflection. -/
@[reassoc] theorem e0StrictPositivePolygonPoint_reflection (r : k) (P : ellipticE0 A W) :
    e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r P ≫ (ρ).hom =
      e0StrictPositiveOppositePoint A hπ data D s hs hstart hk hp r P := by
  have hr : (ρ).hom ≫ (O r).hom = (C r).hom := by
    rw [← coefficientShearRootStrictPositiveCoordinates_reflection, ← Category.assoc,
      coefficientShearRootStrictPositivePolygonReflection_involutive, Category.id_comp]
  apply (cancel_mono (O r).hom).mp
  rw [Category.assoc, hr, e0StrictPositivePolygonPoint_reconstruction,
    e0StrictPositiveOppositePoint, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Equality in full polygon coordinates is exactly equality of original arithmetic reductions. -/
theorem e0StrictPositivePolygonPoint_eq_iff (r : k) (P Q : ellipticE0 A W) :
    e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r P =
        e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r Q ↔
      smoothReductionHom A W P = smoothReductionHom A W Q := by
  rw [e0StrictPositivePolygonPoint, e0StrictPositivePolygonPoint, cancel_mono]
  exact e0CoefficientSection_eq_iff A hπ data k r (s + 1) hs P Q

variable [IsAdicComplete (maximalIdeal A) A]

/-- Original prime-to-residue torsion is distinguished by the full polygon coordinates. -/
theorem e0StrictPositivePolygonPoint_injOn_torsion
    (r : k) (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m) :
    Set.InjOn (e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r)
      {P | m • P = 0} := by
  intro P hP Q hQ h
  exact smoothReductionHom_injOn_torsion_of_not_dvd A W p m hm hP hQ
    ((e0StrictPositivePolygonPoint_eq_iff A hπ data D s hs hstart hk hp r P Q).mp h)

variable [IsDiscreteValuationRing A]

/-- Small-ramification residue-prime torsion also remains distinct in the full polygon. -/
theorem e0StrictPositivePolygonPoint_injOn_small_ramification
    (r : k) (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (e0StrictPositivePolygonPoint A hπ data D s hs hstart hk hp r)
      {P | p • P = 0} := by
  intro P hP Q hQ h
  exact smoothReduction_prime_torsion_injective_small_ramification A W p hp0 he P Q hP hQ
    ((e0StrictPositivePolygonPoint_eq_iff A hπ data D s hs hstart hk hp r P Q).mp h)

end FLT.Mazur.WeierstrassDividedDepth
