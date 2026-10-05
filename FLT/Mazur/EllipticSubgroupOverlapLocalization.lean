/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapClosure

/-!
# Closure overlaps are principal localizations

Quotienting the ambient overlap by the localized subgroup equations commutes
with localization. Consequently the overlap equivalence identifies actual
principal opens of the two chart closures.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The homogeneous coordinate on the subgroup chart closure. -/
def closureCoord (i : Fin 3) : Closure A W H j := Ideal.Quotient.mk _ (coord W j i)

instance : Algebra (Closure A W H j) (OverlapClosure A W H j k) :=
  inferInstanceAs (Algebra (Coordinate W j ⧸ RingHom.ker (coordinateMap A W H j).toRingHom)
    (Overlap W j k ⧸ (RingHom.ker (coordinateMap A W H j).toRingHom).map
      (algebraMap (Coordinate W j) (Overlap W j k))))

instance : IsScalarTower A (Closure A W H j) (OverlapClosure A W H j k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl

set_option backward.isDefEq.respectTransparency false in
instance : IsLocalization.Away (closureCoord A W H j k) (OverlapClosure A W H j k) := by
  have h := (inferInstance : IsLocalization
    (Algebra.algebraMapSubmonoid (Closure A W H j) (Submonoid.powers (coord W j k)))
    (Overlap W j k ⧸ (RingHom.ker (coordinateMap A W H j).toRingHom).map
      (algebraMap (Coordinate W j) (Overlap W j k))))
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    Ideal.Quotient.algebraMap_eq, closureCoord, OverlapClosure, overlapIdeal,
    IsLocalization.Away, instAlgebraClosureOverlapClosure] using h

/-- The principal localization of a subgroup chart closure. -/
abbrev LocalizedClosure := Localization.Away (closureCoord A W H j k)

/-- Taking the closure equations and taking a principal open commute. -/
def closureLocalizationEquiv :
    LocalizedClosure A W H j k ≃ₐ[A] OverlapClosure A W H j k :=
  (IsLocalization.algEquiv (Submonoid.powers (closureCoord A W H j k))
    (LocalizedClosure A W H j k) (OverlapClosure A W H j k)).restrictScalars A

/-- The chart change identifies actual localizations of the two closure algebras. -/
def localizedClosureEquiv :
    LocalizedClosure A W H k j ≃ₐ[A] LocalizedClosure A W H j k :=
  (closureLocalizationEquiv A W H k j).trans
    ((closureOverlapEquiv A W H j k).trans (closureLocalizationEquiv A W H j k).symm)

/-- Localization followed by the overlap quotient has the expected coordinate values. -/
@[simp] theorem closureLocalizationEquiv_coord (i : Fin 3) :
    closureLocalizationEquiv A W H j k
      (algebraMap (Closure A W H j) (LocalizedClosure A W H j k) (closureCoord A W H j i)) =
      Ideal.Quotient.mk _ (overlapCoord W j k i) := by
  exact (IsLocalization.algEquiv (Submonoid.powers (closureCoord A W H j k))
    (LocalizedClosure A W H j k) (OverlapClosure A W H j k)).commutes _

end FLT.Mazur.EllipticSubgroupChart
