/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeScalarLocalRankFiniteness
public import FLT.Mazur.RelativeRankCollisionValuations

/-!
# Full finite endpoint pullbacks control valuative collisions

A valuative lift preserves original endpoint rank when the full original
source over that endpoint is finite. If a colliding generic pair lifts to
a noncolliding closed pair, at least one full endpoint pullback is nonfinite.
The finiteness condition concerns the entire valuation scheme, not its fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (x y : T ⟶ A) {R : Type} [CommRing R]
  (s : T ⟶ Spec (.of R)) (V : ValuativeCommSq s) (l : V.commSq.LiftStruct)

/-- Full finite endpoint geometry transports the actual generic rank to the lifted closed rank. -/
theorem rank_square_lift_iff_of_finite
    [IsFinite (pullback.snd E.hom (l.l ≫ x))] (n : ℕ) :
    x (V.i₁ default) ∈ exactRank E n ↔
      x (l.l (closedPoint V.R)) ∈ exactRank E n := by
  let z := Spec.map (CommRingCat.ofHom (algebraMap V.R V.K)) default
  have he : l.l z = V.i₁ default :=
    congrArg (fun f : Spec (.of V.K) ⟶ T ↦ f default) l.fac_left
  have h := exactRank_local_iff_closedPoint E (l.l ≫ x) z n
  change x (l.l z) ∈ exactRank E n ↔ x (l.l (closedPoint V.R)) ∈ exactRank E n at h
  rwa [he] at h

/-- Both full finite endpoint pullbacks preserve absence of collisions along a valuative lift. -/
theorem not_rankCollision_of_finite_lift
    [IsFinite (pullback.snd E.hom (l.l ≫ x))]
    [IsFinite (pullback.snd E.hom (l.l ≫ y))]
    (hc : l.l (closedPoint V.R) ∉ rankCollision E x y) :
    V.i₁ default ∉ rankCollision E x y := by
  obtain ⟨n, hx, hy⟩ := (not_mem_rankCollision_iff E x y _).mp hc
  apply (not_mem_rankCollision_iff E x y _).mpr
  exact ⟨n, (rank_square_lift_iff_of_finite E x s V l n).mpr hx,
    (rank_square_lift_iff_of_finite E y s V l n).mpr hy⟩

/-- An actual collision with a matching closed lift forces genuine full-source nonfiniteness. -/
theorem rankCollision_lift_not_finite
    (hg : V.i₁ default ∈ rankCollision E x y)
    (hc : l.l (closedPoint V.R) ∉ rankCollision E x y) :
    ¬ IsFinite (pullback.snd E.hom (l.l ≫ x)) ∨
      ¬ IsFinite (pullback.snd E.hom (l.l ≫ y)) := by
  by_cases hx : IsFinite (pullback.snd E.hom (l.l ≫ x))
  · right
    intro hy
    let _ := hx
    let _ := hy
    exact not_rankCollision_of_finite_lift E x y s V l hc hg
  · exact Or.inl hx

end FLT.Mazur.RelativeOrderedTuples
