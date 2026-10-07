/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicEmbedding
public import FLT.EllipticCurve.CubicUniversalCyclicParameters

/-! # The universal prime cyclic subgroup over Weierstrass coefficient space

This is the actual finite étale group family over the universal cyclic
parameter scheme. Its closed inclusion lands in the universal elliptic
curve's torsion, pulled back to the parameter scheme. Each geometric
fiber has p points. Quotienting coordinate changes and adjoining cusps
are still separate constructions.
-/

open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts

/-- The universal cyclic incidence group over the space of Weierstrass cyclic parameters. -/
abbrev universalCyclicGroup (p : ℕ) [NeZero p] :
    Over (universalCyclicParameters p).left :=
  cyclicFamilyModel (levelCurve p) p

/-- The universal torsion group pulled back to the space of cyclic parameters. -/
abbrev universalCyclicAmbientGroup (p : ℕ) [NeZero p] :
    Over (universalCyclicParameters p).left :=
  cyclicAmbientGroup (levelCurve p) p

/-- The actual inclusion of the universal cyclic family into the pulled-back torsion group. -/
abbrev universalCyclicGroupInclusion (p : ℕ) [NeZero p] :
    universalCyclicGroup p ⟶ universalCyclicAmbientGroup p :=
  cyclicFamilyInclusion (levelCurve p) p

/-- The universal cyclic family has a commutative relative group law. -/
abbrev universalCyclicGroupCommGrp (p : ℕ) [Fact p.Prime] [NeZero p] :
    CommGrpObj (universalCyclicGroup p) := inferInstance

/-- The universal cyclic family is finite étale over its parameter scheme. -/
theorem universalCyclicGroup_finite_etale (p : ℕ) [Fact p.Prime] [NeZero p] :
    IsFinite (universalCyclicGroup p).hom ∧ Etale (universalCyclicGroup p).hom :=
  ⟨inferInstance, inferInstance⟩

/-- The universal cyclic family embeds as a closed subgroup of the actual torsion group. -/
theorem universalCyclicGroup_closed_subgroup (p : ℕ) [Fact p.Prime] [NeZero p] :
    IsClosedImmersion (universalCyclicGroupInclusion p).left ∧
      IsMonHom (universalCyclicGroupInclusion p) :=
  ⟨inferInstance, inferInstance⟩

/-- Every geometric fiber of the universal cyclic group has order p. -/
theorem universalCyclicGroup_fiber_card (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [Algebra (LevelBase p) K] [IsAlgClosed K]
    (q : pointSource (R := LevelBase p) K ⟶ universalCyclicParameters p) :
    Nat.card {z : Spec (.of K) ⟶ (universalCyclicGroup p).left //
      z ≫ (universalCyclicGroup p).hom = q.left} = p :=
  cyclicIncidenceFiber_card (levelCurve p) p K q

end WeierstrassCurve.CubicCharts
