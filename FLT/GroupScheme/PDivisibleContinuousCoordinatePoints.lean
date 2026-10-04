/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinateTopology

/-! # Continuous prorepresentation of the original point functor -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace C] [DiscreteTopology C]

/-- The discrete uniformity used only on the original finite coordinate algebras. -/
local instance continuousCoordinateLevelUniformSpace (n : ℕ) : UniformSpace (X.level n).CoordinateRing := ⊥
local instance continuousCoordinateLevelDiscreteUniformity (n : ℕ) : DiscreteUniformity (X.level n).CoordinateRing := ⟨rfl⟩

/-- Continuity into a discrete test algebra is exactly annihilation of a level ideal. -/
theorem continuous_coordinateMap_iff (f : X.coordinateLimit →ₐ[R] B) :
    Continuous f ↔ ∃ n, X.coordinateIdeal n ≤ RingHom.ker f := by
  constructor
  · intro hf
    have hU : IsOpen {x : X.coordinateLimit | f x = 0} :=
      (isOpen_discrete {0}).preimage hf
    obtain ⟨n, hn⟩ := X.coordinateEval_fiber_basis hU 0 (map_zero f)
    refine ⟨n, fun x hx ↦ hn ?_⟩
    change X.coordinateEval n x = X.coordinateEval n 0
    exact hx.trans (map_zero _).symm
  · intro hf
    obtain ⟨x, rfl⟩ := (X.mem_range_pointCoordinateMap f).mpr hf
    induction x using Quotient.ind with
    | _ x =>
      change Continuous (fun a ↦ x.2 (X.coordinateEval x.1 a))
      exact (continuous_of_discreteTopology (f := x.2)).comp
        (X.coordinateEval_uniformContinuous x.1).continuous

/-- Continuous algebra maps out of the original coordinate limit are the original points. -/
def continuousPointCoordinateEquiv :
    X.PointColimit B ≃ {f : X.coordinateLimit →ₐ[R] B // Continuous f} :=
  X.pointCoordinateEquiv.trans
    { toFun := fun f ↦ ⟨f.val, (X.continuous_coordinateMap_iff f.val).mpr f.property⟩
      invFun := fun f ↦ ⟨f.val, (X.continuous_coordinateMap_iff f.val).mp f.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The continuous equivalence uses the original coordinate evaluation at every level. -/
theorem continuousPointCoordinateEquiv_mk (n : ℕ) (f : (X.level n).CoordinateRing →ₐ[R] B) :
    (X.continuousPointCoordinateEquiv (X.pointColimitMk n f)).val =
      f.comp (X.coordinateEval n) := rfl

/-- The continuous representation is natural for maps of discrete test algebras. -/
theorem continuousPointCoordinateEquiv_natural (q : B →ₐ[R] C) (x : X.PointColimit B) :
    (X.continuousPointCoordinateEquiv (X.pointColimitMap q x)).val =
      q.comp (X.continuousPointCoordinateEquiv x).val := X.pointCoordinateMap_natural q x

end ThreeAdicPlan.PDivisibleSystem
