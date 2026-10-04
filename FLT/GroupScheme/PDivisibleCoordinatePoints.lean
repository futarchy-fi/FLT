/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinateQuotient
public import FLT.GroupScheme.PDivisiblePointColimit

/-! # Prorepresentation of the original point colimit by its coordinate algebra

The ideal-containment condition describes maps to discrete test algebras for the
level-ideal topology. No identification with a power-series algebra is asserted.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- An original point evaluates compatible coordinate functions at any representing level. -/
def pointCoordinateMap : X.PointColimit B → (X.coordinateLimit →ₐ[R] B) :=
  DirectLimit.lift _ (fun n f ↦ f.comp (X.coordinateEval n)) (by
    intro m n h f
    ext x
    exact congrArg f (X.coordinateEval_inclusion h x).symm)

/-- At a finite level the representing map is exactly composition with evaluation. -/
theorem pointCoordinateMap_mk (n : ℕ) (f : (X.level n).CoordinateRing →ₐ[R] B) :
    X.pointCoordinateMap (X.pointColimitMk n f) = f.comp (X.coordinateEval n) := rfl

/-- The representing map retains the original point, since every evaluation is surjective. -/
theorem pointCoordinateMap_injective : Function.Injective (X.pointCoordinateMap (B := B)) := by
  apply DirectLimit.lift_injective
  intro n f g h
  ext a
  obtain ⟨x, rfl⟩ := X.coordinateEval_surjective n a
  exact AlgHom.congr_fun h x

/-- Maps represented by original points are exactly those killing some original level ideal. -/
theorem mem_range_pointCoordinateMap (f : X.coordinateLimit →ₐ[R] B) :
    f ∈ Set.range X.pointCoordinateMap ↔ ∃ n, X.coordinateIdeal n ≤ RingHom.ker f := by
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ x =>
      refine ⟨x.1, ?_⟩
      intro a ha
      change x.2 (X.coordinateEval x.1 a) = 0
      change X.coordinateEval x.1 a = 0 at ha
      rw [ha, map_zero]
  · rintro ⟨n, hn⟩
    let g := AlgHom.liftOfSurjective (X.coordinateEval n) (X.coordinateEval_surjective n) f hn
    exact ⟨X.pointColimitMk n g,
      AlgHom.liftOfSurjective_comp (X.coordinateEval n) (X.coordinateEval_surjective n) f hn⟩

/-- The original point functor is represented by the coordinate limit with its level ideals. -/
def pointCoordinateEquiv : X.PointColimit B ≃
    {f : X.coordinateLimit →ₐ[R] B // ∃ n, X.coordinateIdeal n ≤ RingHom.ker f} :=
  Equiv.ofBijective
    (fun x ↦ ⟨X.pointCoordinateMap x, (X.mem_range_pointCoordinateMap _).mp ⟨x, rfl⟩⟩)
    ⟨fun _ _ h ↦ X.pointCoordinateMap_injective (congrArg Subtype.val h), by
      rintro ⟨f, hf⟩
      obtain ⟨x, hx⟩ := (X.mem_range_pointCoordinateMap f).mpr hf
      exact ⟨x, Subtype.ext hx⟩⟩

/-- The representing equivalence agrees with every original finite point. -/
theorem pointCoordinateEquiv_mk (n : ℕ) (f : (X.level n).CoordinateRing →ₐ[R] B) :
    (X.pointCoordinateEquiv (X.pointColimitMk n f)).val = f.comp (X.coordinateEval n) := rfl

/-- Prorepresentation is natural in the test algebra. -/
theorem pointCoordinateMap_natural (q : B →ₐ[R] C) (x : X.PointColimit B) :
    X.pointCoordinateMap (X.pointColimitMap q x) = q.comp (X.pointCoordinateMap x) := by
  induction x using Quotient.ind with | _ x => rfl

end ThreeAdicPlan.PDivisibleSystem
