/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleContinuousCoordinatePoints
public import FLT.GroupScheme.PDivisibleFormalSmoothness

/-! # Continuous nilpotent lifting for the original representing algebra -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace C] [DiscreteTopology C]

/-- The constructed representing algebra lifts continuous maps across nilpotent
extensions of p-nilpotent discrete test algebras, using original point lifting. -/
theorem exists_continuous_coordinate_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : IsNilpotent (RingHom.ker q)) (hB : IsNilpotent (p : B))
    (f : X.coordinateLimit →ₐ[R] C) (hf : Continuous f) :
    ∃ g : X.coordinateLimit →ₐ[R] B, Continuous g ∧ q.comp g = f := by
  let x := (X.continuousPointCoordinateEquiv (B := C)).symm ⟨f, hf⟩
  obtain ⟨y, hy⟩ := X.pointColimitMap_surjective_nilpotent q hq hJ hB x
  refine ⟨(X.continuousPointCoordinateEquiv y).val,
    (X.continuousPointCoordinateEquiv y).property, ?_⟩
  rw [← X.continuousPointCoordinateEquiv_natural, hy]
  exact congrArg Subtype.val ((X.continuousPointCoordinateEquiv (B := C)).apply_symm_apply ⟨f, hf⟩)

omit [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace C] [DiscreteTopology C] in
/-- A continuous map at a specified original level lifts continuously and still factors
through an original finite level; no formal smoothness hypothesis is added to the algebra. -/
theorem exists_coordinate_level_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : IsNilpotent (RingHom.ker q)) (hB : IsNilpotent (p : B))
    (n : ℕ) (f : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ (m : ℕ) (g : (X.level m).CoordinateRing →ₐ[R] B),
      q.comp (g.comp (X.coordinateEval m)) = f.comp (X.coordinateEval n) := by
  obtain ⟨m, h, g, hg⟩ := X.exists_nilpotent_inclusion_lift q hq hJ hB n f
  refine ⟨m, g, ?_⟩
  ext x
  have he := AlgHom.congr_fun hg (X.coordinateEval m x)
  exact he.trans (congrArg f (X.coordinateEval_inclusion h x))

end ThreeAdicPlan.PDivisibleSystem
