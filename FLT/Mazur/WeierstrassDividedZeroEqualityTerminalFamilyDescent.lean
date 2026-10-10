/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityCycleTerminalDescent

public import FLT.Mazur.PolygonPinchingDiagram

/-!
# Terminal node descent from the full compatible equality-cycle family

For positive-depth terminal nodes, the maps use the actual cyclic indices and
reciprocal tangent scales. The same full terminal component supplies both endpoints.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "ν" => Spec.map
  (CommRingCat.ofHom (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (conicParameterNeg c))))

local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
variable {Y : Scheme.{u}}
  (f : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ f i =
    ProjectiveLine.infinity (ResidueField R) ≫ f (PolygonPinching.next (by omega) i))

include w in
/-- A compatible cyclic family descends uniquely on the first original terminal attachment. -/
theorem zeroEqualityCycle_terminal_first_exists_unique_desc :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleParameterConicBranch c ≫ d = q₁ ≫ ρ ≫ f ⟨s + 1, by omega⟩ ∧
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleParameterLineBranch c ≫ d =
        ProjectiveLine.left K ≫ f ⟨s, by omega⟩ := by
  apply equalityCycleTerminalFirst_exists_unique_desc data D s hs hk hp (tangent)⁻¹
  have hn : PolygonPinching.next (by omega) (⟨s, by omega⟩ : Fin (2 * s + 2)) =
      ⟨s + 1, by omega⟩ := by
    apply Fin.ext
    change (s + 1) % (2 * s + 2) = s + 1
    exact Nat.mod_eq_of_lt (by omega)
  simpa only [hn] using w ⟨s, by omega⟩

include w in
/-- For positive cycle length the outgoing terminal node descends with the opposite sign. -/
theorem zeroEqualityCycle_terminal_second_exists_unique_desc (hpos : 0 < s) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleParameterConicBranch c ≫ d = ν ≫ q₂ ≫ ρ ≫ f ⟨s + 1, by omega⟩ ∧
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleParameterLineBranch c ≫ d =
        ProjectiveLine.right K ≫ f ⟨s + 2, by omega⟩ := by
  apply equalityCycleTerminalSecond_exists_unique_desc data D s hs hk hp (-tangent)⁻¹
  have hn : PolygonPinching.next (by omega) (⟨s + 1, by omega⟩ : Fin (2 * s + 2)) =
      ⟨s + 2, by omega⟩ := by
    apply Fin.ext
    change (s + 1 + 1) % (2 * s + 2) = s + 2
    exact Nat.mod_eq_of_lt (by omega)
  simpa only [hn] using w ⟨s + 1, by omega⟩

end FLT.Mazur.WeierstrassDividedDepth
