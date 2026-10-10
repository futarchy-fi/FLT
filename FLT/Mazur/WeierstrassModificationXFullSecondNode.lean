/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeBranches
public import FLT.Mazur.WeierstrassModificationXFiberTangentSwitch

/-!
# The second full ambient node with its original tangent orientation

The actual localization at v is recentered by v ↦ w-a. The first full
node comparison then applies with coefficient -a and the same c.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)

/-- The second tangent neighborhood of the full original fiber. -/
abbrev FullSecondFiberOpen := Localization.Away (fiberV a c)

/-- Translation of the original slope identifies the actual tangent neighborhoods. -/
def fullSecondFiberOpenEquiv : FullSecondFiberOpen a c ≃ₐ[R] FullFirstFiberOpen (-a) c :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (fiberV a c))
    (T := Submonoid.powers (fiberV (-a) c + algebraMap R _ (-a)))
    _ _ (fiberTangentEquiv a c) (by
      rw [Submonoid.map_powers, fiberTangentEquiv_v])

/-- The localized translation retains the original fiber coordinate substitution. -/
theorem fullSecondFiberOpenEquiv_base (x : FiberCoordinate a c) :
    fullSecondFiberOpenEquiv a c (algebraMap _ _ x) =
      algebraMap _ _ (fiberTangentEquiv a c x) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ x

/-- The second full ambient neighborhood is the oppositely oriented node open. -/
def fullSecondNodeEquiv : FullSecondFiberOpen a c ≃ₐ[R] FullNodeOpen (-a) c :=
  (fullSecondFiberOpenEquiv a c).trans (fullFirstNodeEquiv (-a) c ha.neg)

/-- The second chart retains the original incidence coordinate. -/
theorem fullSecondNodeEquiv_t :
    fullSecondNodeEquiv a c ha (algebraMap _ _ (fiberT a c)) =
      fullNodeInverseT (-a) c := by
  rw [fullSecondNodeEquiv, AlgEquiv.trans_apply, fullSecondFiberOpenEquiv_base,
    fiberTangentEquiv_t, fullFirstNodeEquiv_t]

/-- The recentered slope is the original second tangent factor v+a. -/
theorem fullSecondNodeEquiv_second :
    fullSecondNodeEquiv a c ha (algebraMap _ _ (fiberV a c + algebraMap R _ a)) =
      fullNodeInverseV (-a) c := by
  rw [fullSecondNodeEquiv, AlgEquiv.trans_apply, fullSecondFiberOpenEquiv_base,
    fiberTangentEquiv_second, fullFirstNodeEquiv_v]

/-- The original slope differs from the second inverse slope by exactly a. -/
theorem fullSecondNodeEquiv_v :
    fullSecondNodeEquiv a c ha (algebraMap _ _ (fiberV a c)) =
      fullNodeInverseV (-a) c - algebraMap R _ a := by
  have h := fullSecondNodeEquiv_second a c ha
  rw [map_add, ← IsScalarTower.algebraMap_apply R (FiberCoordinate a c)
    (FullSecondFiberOpen a c), map_add, AlgEquiv.commutes] at h
  exact eq_sub_of_add_eq h

include ha in
/-- The two full fiber tangent opens cover for a unit tangent difference. -/
theorem fullFiber_tangent_opens_cover (p : PrimeSpectrum (FiberCoordinate a c)) :
    fiberV a c + algebraMap R _ a ∉ p.asIdeal ∨ fiberV a c ∉ p.asIdeal := by
  by_cases hv : fiberV a c ∈ p.asIdeal
  · left
    intro hu
    have h : algebraMap R _ a ∈ p.asIdeal := by
      simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem hu hv
    exact p.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h (ha.map (algebraMap R (FiberCoordinate a c))))
  · exact Or.inr hv

end FLT.Mazur.WeierstrassModificationX
