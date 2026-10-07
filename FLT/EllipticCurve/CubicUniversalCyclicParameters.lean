/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicEtale
public import FLT.EllipticCurve.CubicLevelParameters
/-! # Universal prime cyclic parameters for Weierstrass equations

The prime scalar quotient over the universal coefficient ring is finite étale and
surjective. Its geometric fibers classify subgroups of order p and have
p+1 points. A rational generator also supplies an actual rational point
of this parameter scheme. Quotienting changes of Weierstrass coordinates
and adjoining cusps are not part of this construction.
-/

open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts

instance levelBaseOrderUnit (n : ℕ) : Fact (IsUnit (n : LevelBase n)) :=
  ⟨(levelBase_units n).1⟩

/-- The universal scalar quotient of nonzero torsion over the coefficient space. -/
abbrev universalCyclicParameters (p : ℕ) [NeZero p] :
    Over (Spec (.of (LevelBase p))) :=
  scalarQuotientModel (levelCurve p) p

/-- The universal map forgetting the choice of a nonzero prime-torsion generator. -/
def universalCyclicGeneratorMap (p : ℕ) [NeZero p] :
    universalNonzeroTorsion p ⟶ universalCyclicParameters p :=
  scalarQuotientMap (levelCurve p) p

/-- The universal cyclic parameter scheme is finite over the coefficient space. -/
theorem universalCyclicParameters_finite (p : ℕ) [NeZero p] :
    IsFinite (universalCyclicParameters p).hom :=
  scalarQuotientModel_finite (levelCurve p) p

/-- Forgetting the generator is a finite morphism. -/
theorem universalCyclicGeneratorMap_finite (p : ℕ) [NeZero p] :
    IsFinite (universalCyclicGeneratorMap p).left :=
  scalarQuotientMap_finite (levelCurve p) p

/-- Forgetting the generator is surjective on the underlying schemes. -/
theorem universalCyclicGeneratorMap_surjective (p : ℕ) [NeZero p] :
    Surjective (universalCyclicGeneratorMap p).left :=
  scalarQuotientMap_surjective (levelCurve p) p

/-- The universal prime cyclic parameter scheme is étale over the coefficient space. -/
theorem universalCyclicParameters_etale (p : ℕ) [Fact p.Prime] [NeZero p] :
    Etale (universalCyclicParameters p).hom :=
  scalarQuotientModel_etale (levelCurve p) p

/-- Forgetting a universal prime generator is an étale morphism. -/
theorem universalCyclicGeneratorMap_etale (p : ℕ) [Fact p.Prime] [NeZero p] :
    Etale (universalCyclicGeneratorMap p).left :=
  scalarQuotientMap_etale (levelCurve p) p

/-- Every coefficient point has a prime cyclic parameter above it. -/
theorem universalCyclicParameters_surjective (p : ℕ) [Fact p.Prime] [NeZero p] :
    Surjective (universalCyclicParameters p).hom := by
  constructor
  intro x
  obtain ⟨y, hy⟩ :=
    (universalNonzeroTorsion_surjective p (Fact.out : p.Prime).one_lt).1 x
  refine ⟨(universalCyclicGeneratorMap p).left y, ?_⟩
  change ((universalCyclicGeneratorMap p).left ≫ (universalCyclicParameters p).hom) y = x
  rw [(universalCyclicGeneratorMap p).w]
  exact hy

/-- Over a chosen geometric elliptic equation, the fiber classifies prime-order subgroups. -/
def universalCyclicFieldPointEquiv (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [IsAlgClosed K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] (hp : IsUnit (p : K)) :
    (letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra;
      pointSource (R := LevelBase p) K ⟶ universalCyclicParameters p) ≃
      {H : AddSubgroup E.toAffine.Point // Nat.card H = p} := by
  letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra
  let e := scalarQuotientPrimeSubgroupEquiv (levelCurve p) p K
  exact e.trans (Equiv.cast (congrArg
    (fun C : WeierstrassCurve K => {H : AddSubgroup C.toAffine.Point // Nat.card H = p})
    (levelCurve_specialize E p hp)))

/-- The geometric fiber over any elliptic equation contains p+1 points. -/
theorem universalCyclicFieldPoints_card (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [IsAlgClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic] (hp : IsUnit (p : K)) :
    (letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra;
      Nat.card (pointSource (R := LevelBase p) K ⟶ universalCyclicParameters p)) = p + 1 := by
  let : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra
  exact scalarQuotientFieldPoints_card (levelCurve p) p K

/-- A rational prime-order generator gives a rational universal cyclic parameter. -/
def universalCyclicPointOfGenerator (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] (hp : IsUnit (p : K))
    (P : E.toAffine.Point) (hP : addOrderOf P = p) :
    letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra;
      pointSource (R := LevelBase p) K ⟶ universalCyclicParameters p := by
  letI : Algebra (LevelBase p) K := (levelSpecialize E p hp).toAlgebra
  exact (universalPrimeLevelFieldPointEquiv p K E hp).symm ⟨P, hP⟩ ≫
    universalCyclicGeneratorMap p

end WeierstrassCurve.CubicCharts
