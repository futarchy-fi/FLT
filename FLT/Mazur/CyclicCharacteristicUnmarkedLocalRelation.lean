/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSheaf

/-!
# The exact local relation of the unmarked fppf quotient

Two parameters have equal sheaf images exactly when full compatible
comparisons exist on an fppf covering sieve. The comparisons need not glue
to a global isomorphism. This distinguishes the sheaf quotient kernel from
the original pointwise relation, including at non-etale cyclic levels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Tests on which the original full curves and subgroups are compatibly isomorphic. -/
def unmarkedComparisonSieve (q r : NormalizedParameter n T) : Sieve T where
  arrows U g := (normalizedParameterSetoid n U).r
    ((normalizedParameterPresheaf n).map g.op q) ((normalizedParameterPresheaf n).map g.op r)
  downward_closed {U V} {g} h e := by
    change UnmarkedRelated n q.1 r.1 (g ≫ q.2.down) (g ≫ r.2.down) at h
    change UnmarkedRelated n q.1 r.1 ((e ≫ g) ≫ q.2.down) ((e ≫ g) ≫ r.2.down)
    simpa only [Category.assoc] using UnmarkedRelated.baseChange n h e

/-- The comparison sieve is the equality sieve of the actual pointwise quotient. -/
theorem unmarkedComparisonSieve_eq (q r : NormalizedParameter n T) :
    unmarkedComparisonSieve n q r = Presheaf.equalizerSieve
      (F := unmarkedParameterClassPresheaf n)
      ((unmarkedParameterProjection n).app (Opposite.op T) q)
      ((unmarkedParameterProjection n).app (Opposite.op T) r) := by
  ext U g
  exact Quotient.eq.symm

/-- Full compatible comparisons exist fppf locally, without prescribed auxiliary markings. -/
def LocallyUnmarkedRelated (q r : NormalizedParameter n T) : Prop :=
  unmarkedComparisonSieve n q r ∈ Scheme.fppfTopology T

/-- Equality in the constructed sheaf is exactly fppf-local full compatible comparison. -/
theorem unmarkedParameterSheafMap_eq_iff (q r : NormalizedParameter n T) :
    (unmarkedParameterSheafMap n).app (Opposite.op T) q =
      (unmarkedParameterSheafMap n).app (Opposite.op T) r ↔
        LocallyUnmarkedRelated n q r := by
  change _ ↔ unmarkedComparisonSieve n q r ∈ Scheme.fppfTopology T
  rw [unmarkedComparisonSieve_eq]
  constructor
  · exact Presheaf.equalizerSieve_mem Scheme.fppfTopology
      (toSheafify _ (unmarkedParameterClassPresheaf n)) _ _
  · intro h
    apply (((isSheaf_iff_isSheaf_of_type _ _).mp
      (unmarkedParameterSheaf n).property).isSeparated _ h).ext
    intro U g hg
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg ((unmarkedClassToSheaf n).app (Opposite.op U)) hg

/-- Every global genuine comparison is also a local comparison. -/
theorem locallyUnmarkedRelated_of_related {q r : NormalizedParameter n T}
    (h : (normalizedParameterSetoid n T).r q r) : LocallyUnmarkedRelated n q r := by
  apply (unmarkedParameterSheafMap_eq_iff n q r).mp
  exact congrArg ((unmarkedClassToSheaf n).app (Opposite.op T)) (Quotient.sound h)

/-- The exact local relation is an equivalence relation on actual normalized parameters. -/
def locallyUnmarkedSetoid (T : Scheme) : Setoid (NormalizedParameter n T) :=
  Setoid.comap ((unmarkedParameterSheafMap n).app (Opposite.op T)) ⊥

/-- The equivalence relation just constructed is the geometric covering-sieve predicate. -/
theorem locallyUnmarkedSetoid_iff (q r : NormalizedParameter n T) :
    (locallyUnmarkedSetoid n T).r q r ↔ LocallyUnmarkedRelated n q r :=
  unmarkedParameterSheafMap_eq_iff n q r

/-- Local unmarked comparisons survive arbitrary base change. -/
theorem LocallyUnmarkedRelated.baseChange {q r : NormalizedParameter n T}
    (h : LocallyUnmarkedRelated n q r) {U : Scheme} (g : U ⟶ T) :
    LocallyUnmarkedRelated n ((normalizedParameterPresheaf n).map g.op q)
      ((normalizedParameterPresheaf n).map g.op r) := by
  apply (unmarkedParameterSheafMap_eq_iff n _ _).mp
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
  exact congrArg ((unmarkedParameterSheaf n).obj.map g.op)
    ((unmarkedParameterSheafMap_eq_iff n q r).mpr h)

/-- A specified small fppf comparison cover witnesses equality in the actual sheaf quotient. -/
theorem locallyUnmarkedRelated_of_cover (q r : NormalizedParameter n T)
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T)
    (h : ∀ i, (normalizedParameterSetoid n (C.X i)).r
      ((normalizedParameterPresheaf n).map (C.f i).op q)
      ((normalizedParameterPresheaf n).map (C.f i).op r)) : LocallyUnmarkedRelated n q r := by
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro U g ⟨i⟩
  exact h i

end FLT.Mazur.CyclicCharacteristicAtlas
