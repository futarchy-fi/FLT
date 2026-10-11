/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps

/-!
# The full terminal retained tensor map and its entire conic restriction

Pulling the glued indexed map back to the original tensor chart recovers both
ordered node maps. Their parameter restrictions determine the entire conic map,
with no reduction or separatedness assumption on the target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "V" => olderSuccessiveTensorAtlasIso hπ data K s hs 0 hs
local notation "N₁" => residueMiddleFirstNodeChart D (start + s) (by omega) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueMiddleSecondNodeChart D (start + s) (by omega) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "C" => residueSuccessiveConicImmersion D (start + s) (by omega) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "l" => laurentConicComponentConic D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "ν" => Spec.map (CommRingCat.ofHom
  (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (conicParameterNeg c))))
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The whole terminal retained tensor chart carries the original indexed descent. -/
def positiveEqualityCycleTerminalTensorDesc :
    Spec (.of (ScalarExtension W (π ^ (start + s)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  (V).hom ≫ positiveEqualityCycleTerminalIndexedDesc hπ data D s hs hstart hk hp F w
local notation "d" => positiveEqualityCycleTerminalTensorDesc hπ data D s hs hstart hk hp F w

/-- The first original tensor node recovers its full chosen attachment map. -/
@[reassoc] theorem positiveEqualityCycleTerminalTensorDesc_first :
    N₁ ≫ d = positiveEqualityCycleTerminalFirstDesc data D s hs hk hp F w := by
  simpa only [positiveEqualityCycleTerminalTensorDesc, olderIndexedNodeMap, Fin.cases_zero,
    Category.assoc] using
    positiveEqualityCycleTerminalIndexedDesc_first hπ data D s hs hstart hk hp F w

/-- The opposite tensor node recovers the original negative parameter map. -/
@[reassoc] theorem positiveEqualityCycleTerminalTensorDesc_second :
    N₂ ≫ d = positiveEqualityCycleTerminalSecondDesc data D s hs hk hp F w := by
  have H := positiveEqualityCycleTerminalIndexedDesc_second hπ data D s hs hstart hk hp F w
  change (N₂ ≫ (V).hom) ≫
    positiveEqualityCycleTerminalIndexedDesc hπ data D s hs hstart hk hp F w = _ at H
  simpa only [positiveEqualityCycleTerminalTensorDesc, Category.assoc] using H

/-- The entire conic restriction is induced by the same complete reversed terminal component. -/
@[reassoc] theorem positiveEqualityCycleTerminalTensorDesc_conic :
    C ≫ d = l ≫ (J).inv ≫ ρ ≫ F ⟨s + 2, by omega⟩ := by
  apply conicParameter_hom_ext a c ha
  · simp only [Category.assoc]
    rw [← residueMiddleFirstNodeChart_parameterConicBranch_assoc,
      positiveEqualityCycleTerminalTensorDesc_first, positiveEqualityCycleTerminalFirstDesc_conic]
    simp only [equalityTerminalFirstNodeParameter, laurentConicComponentFirstParameter,
      Category.assoc, WeierstrassCurve.map_a₁]
  · let _ : IsIso ν := by
      change IsIso (Scheme.Spec.mapIso (conicParameterNeg c).toRingEquiv.toCommRingCatIso.op).hom
      infer_instance
    apply (cancel_epi ν).mp
    simp only [Category.assoc]
    rw [← residueMiddleSecondNodeChart_parameterConicBranch_assoc,
      positiveEqualityCycleTerminalTensorDesc_second, positiveEqualityCycleTerminalSecondDesc_conic]
    simp only [equalityTerminalSecondNodeParameter, laurentConicComponentSecondParameter,
      Category.assoc, WeierstrassCurve.map_a₁]

end FLT.Mazur.WeierstrassDividedDepth
