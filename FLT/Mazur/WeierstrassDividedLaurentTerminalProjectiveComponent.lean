/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLaurentTerminalAttachments
public import FLT.Mazur.WeierstrassDividedLaurentTerminalEmbedding
public import FLT.Mazur.WeierstrassSuccessiveXTerminalProjectiveStructure

/-!
# The complete terminal projective component in the original finite model

The actual projective line maps through the original conic/Laurent gluing.
Its image and coefficients are unchanged; zero and infinity are precisely
the original ordered attachment sections at both possible scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R (Data.b6 d)
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen (W.map (residue R)) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "X" => finiteGlobalTensorModel hπ data K (j + 1) hj

local notation "C" => laurentTerminalOriginalConic hπ data D j hj hk
variable (hp : 2 * (start + j + 1) = depth)
local notation "ψ" => residueLaurentConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj
  (Nat.zero_lt_succ (start + j)) hk hp
local notation "P" => laurentConicComponent D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "l" => laurentConicComponentConic D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "r" => laurentConicComponentTorus D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

local notation "f" => laurentTerminalComponentMap hπ data D j hj hk hp

local notation "p" => laurentConicComponentStructure D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "b" => pullback.fst q (finiteGlobalStructure hπ data (j + 1) hj)

local notation "J" => laurentConicComponentProjectiveIso D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The full equality-depth projective line in the actual finite residue model. -/
def laurentTerminalProjectiveComponent : ProjectiveLine.scheme K ⟶ X := (J).hom ≫ f
local notation "F" => laurentTerminalProjectiveComponent hπ data D j hj hk hp

/-- The entire original Laurent chart is retained, with its original coordinate. -/
@[reassoc] theorem laurentTerminalProjectiveComponent_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ F = G := by
  rw [laurentTerminalProjectiveComponent,
    laurentConicComponentProjectiveIso_torus_assoc, laurentTerminalComponentMap_torus]

/-- The full projective component keeps the original coefficient structure. -/
@[reassoc] theorem laurentTerminalProjectiveComponent_structure : F ≫ b =
    ProjectiveLine.toBase K := by
  rw [laurentTerminalProjectiveComponent, Category.assoc,
    laurentTerminalComponentMap_structure, laurentConicComponentProjectiveIso_structure]

/-- No points are lost or added to the original complete conic and Laurent image. -/
theorem laurentTerminalProjectiveComponent_range : Set.range F =
    Set.range C ∪ Set.range G := by
  change Set.range (fun x => f ((J).hom x)) = _
  exact ((J).hom.homeomorph.surjective.range_comp f).trans
    (laurentTerminalComponentMap_range hπ data D j hj hk hp)

/-- The projective parametrization introduces no extra point identifications. -/
theorem laurentTerminalProjectiveComponent_injective : Function.Injective F :=
  (laurentTerminalComponentMap_injective hπ data D j hj hk hp).comp
    (J).hom.homeomorph.injective

/-- At positive scale, zero is the original first ordered attachment. -/
@[reassoc] theorem laurentTerminalProjectiveComponent_zero_positive (h : 0 < start + j) :
    ProjectiveLine.zero K ≫ F = olderGlobalFirstSection hπ data D j hj 0 hj h hk := by
  rw [laurentTerminalProjectiveComponent, ← Category.assoc,
    laurentConicComponentProjectiveIso_zero,
    laurentTerminalComponentMap_first_positive hπ data D j hj hk hp h]

/-- At scale one, zero remains the original initial first attachment. -/
@[reassoc] theorem laurentTerminalProjectiveComponent_zero (h : start + j = 0) :
    ProjectiveLine.zero K ≫ F = olderGlobalZeroFirstSection hπ data D j hj 0 hj h hk := by
  rw [laurentTerminalProjectiveComponent, ← Category.assoc,
    laurentConicComponentProjectiveIso_zero,
    laurentTerminalComponentMap_first_zero hπ data D j hj hk hp h]

/-- At positive scale, infinity is the original opposite ordered attachment. -/
@[reassoc] theorem laurentTerminalProjectiveComponent_infinity_positive (h : 0 < start + j) :
    ProjectiveLine.infinity K ≫ F = olderGlobalSecondSection hπ data D j hj 0 hj h hk := by
  rw [laurentTerminalProjectiveComponent, ← Category.assoc,
    laurentConicComponentProjectiveIso_infinity,
    laurentTerminalComponentMap_second_positive hπ data D j hj hk hp h]

/-- At scale one, infinity remains the original initial second attachment. -/
@[reassoc] theorem laurentTerminalProjectiveComponent_infinity (h : start + j = 0) :
    ProjectiveLine.infinity K ≫ F = olderGlobalZeroSecondSection hπ data D j hj 0 hj h hk := by
  rw [laurentTerminalProjectiveComponent, ← Category.assoc,
    laurentConicComponentProjectiveIso_infinity,
    laurentTerminalComponentMap_second_zero hπ data D j hj hk hp h]

end FLT.Mazur.WeierstrassDividedDepth
