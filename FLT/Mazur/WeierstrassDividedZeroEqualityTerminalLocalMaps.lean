/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalFamilyDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalFamilyDescent

public import FLT.Mazur.PolygonPinchingDiagram

/-!
# Chosen full terminal attachment maps for an equality-depth family

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

/-- The first full terminal node receives the map determined by the cyclic family. -/
def zeroEqualityCycleTerminalFirstDesc : Spec (.of (MiddleNodeOpen c)) ⟶ Y :=
  (zeroEqualityCycle_terminal_first_exists_unique_desc data D s hs hk hp f w).choose

/-- The conic restriction retains the entire terminal parameter. -/
@[reassoc] theorem zeroEqualityCycleTerminalFirstDesc_conic :
    middleParameterConicBranch c ≫ zeroEqualityCycleTerminalFirstDesc data D s hs hk hp f w =
      q₁ ≫ ρ ≫ f ⟨s + 1, by omega⟩ :=
  (zeroEqualityCycle_terminal_first_exists_unique_desc data D s hs hk hp f w).choose_spec.1.1

/-- The first horizontal restriction retains its reciprocal tangent scale. -/
@[reassoc] theorem zeroEqualityCycleTerminalFirstDesc_line :
    ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleParameterLineBranch c ≫
        zeroEqualityCycleTerminalFirstDesc data D s hs hk hp f w =
      ProjectiveLine.left K ≫ f ⟨s, by omega⟩ :=
  (zeroEqualityCycle_terminal_first_exists_unique_desc data D s hs hk hp f w).choose_spec.1.2

variable (hpos : 0 < s)

/-- The second full terminal node receives the same terminal component map. -/
def zeroEqualityCycleTerminalSecondDesc : Spec (.of (MiddleNodeOpen c)) ⟶ Y :=
  (zeroEqualityCycle_terminal_second_exists_unique_desc data D s hs hk hp f w hpos).choose

/-- The opposite conic restriction retains its original negative parameter. -/
@[reassoc] theorem zeroEqualityCycleTerminalSecondDesc_conic :
    middleParameterConicBranch c ≫
        zeroEqualityCycleTerminalSecondDesc data D s hs hk hp f w hpos =
      ν ≫ q₂ ≫ ρ ≫ f ⟨s + 1, by omega⟩ :=
  (zeroEqualityCycle_terminal_second_exists_unique_desc data D s hs hk hp f w
    hpos).choose_spec.1.1

/-- The opposite horizontal restriction retains the negative reciprocal tangent scale. -/
@[reassoc] theorem zeroEqualityCycleTerminalSecondDesc_line :
    ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleParameterLineBranch c ≫
        zeroEqualityCycleTerminalSecondDesc data D s hs hk hp f w hpos =
      ProjectiveLine.right K ≫ f ⟨s + 2, by omega⟩ :=
  (zeroEqualityCycle_terminal_second_exists_unique_desc data D s hs hk hp f w
    hpos).choose_spec.1.2

end FLT.Mazur.WeierstrassDividedDepth
