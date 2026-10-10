/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicParameters
public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The terminal node origin misses the entire original conic boundary

The ordered coordinate difference is a unit on the conic boundary and
vanishes at the node. This argument also applies at initial depth zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) < depth)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "B" => MiddleConicOpen W₀ c
local notation "v" => conicBoundaryUnit W₀ c
local notation "ψ" => residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "δ" => (PolygonNodeLocalization.y - PolygonNodeLocalization.x :
  PolygonNodeEqualizer.A (R := K))
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "o" => PolygonNodePresentation.aOrigin K

/-- The ordered branch difference is invertible on the whole original conic boundary. -/
theorem residueNodeConicMap_difference_isUnit : IsUnit (ψ δ) := by
  have he : ψ δ = (↑(v)⁻¹ : B) * algebraMap K B (residue R W.a₁) := by
    rw [map_sub, residueNodeConicMap_second, residueNodeConicMap_first]
    ring
  rw [he]
  exact ((v)⁻¹).isUnit.mul ((D.a₁_unit.map (residue R)).map (algebraMap K B))

/-- No point of the original conic boundary can be the terminal node origin. -/
theorem residueNodeConicOrigin_disjoint : Disjoint (Set.range s) (Set.range o) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  have hz : PolygonNodePresentation.aEval δ = 0 := by
    simp [PolygonNodePresentation.aEval]
  have hm : δ ∈ (o q).asIdeal := by
    change PolygonNodePresentation.aEval δ ∈ q.asIdeal
    rw [hz]
    exact q.asIdeal.zero_mem
  rw [hq] at hm
  change ψ δ ∈ p.asIdeal at hm
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm
    (residueNodeConicMap_difference_isUnit D k hk b3 b4 b6 h3 h4 h6 hp))

/-- The complete boundary-origin scheme fiber product is empty. -/
theorem residueNodeConicOrigin_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) s o := by
  let _ := Scheme.isEmpty_pullback _ _
    (residueNodeConicOrigin_disjoint D k hk b3 b4 b6 h3 h4 h6 hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback s o)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassSuccessiveX
