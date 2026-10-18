/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSeed
public import FLT.Mazur.PolygonArithmeticCyclicGeometry

/-!
# Simultaneous normalization of the concrete five-node seed

Start the measured cyclic construction at order zero. Every normalized node
retains its full smoothing drift and both exact original puncture maps.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticCyclic PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "hS" => arithmeticZeroCyclicSeed_compatible hπ data H hj u hu
local notation "ha" => arithmeticZeroCyclicSeed_annihilated hπ data H hj u hu
local notation "hr" => arithmeticZeroCyclicSeed_normalized hπ data H hj u hu
local notation "σ" => zeroCyclicSuccessor
local notation "Q" => fun m ↦ Quotient R π m

/-- The measured all-order diagonal of the concrete five-node exact-twist seed. -/
def arithmeticZeroCyclicDiagonal : State R π ZeroCyclicVertex :=
  (S).diagonal σ hS ha 0 hr

local notation "D" => arithmeticZeroCyclicDiagonal hπ data H hj u hu

/-- All five corrected smoothings and full edges keep the original quotients. -/
theorem arithmeticZeroCyclicDiagonal_compatible : (D).Compatible :=
  (S).diagonal_compatible σ hS ha 0 hr

/-- All five corrected smoothings retain their actual top-power annihilators. -/
theorem arithmeticZeroCyclicDiagonal_annihilated : (D).Annihilated :=
  (S).diagonal_annihilated σ hS ha 0 hr

/-- Every edge, including the common initial pair and both closing edges, is reciprocal. -/
theorem arithmeticZeroCyclicDiagonal_normalized (m : ℕ) : (D).Normalized m :=
  (S).diagonal_normalized σ hS ha 0 hr m

/-- The full comparison on each of the five entire seed nodes. -/
def arithmeticZeroCyclicNodeIso (m : ℕ) (i : ZeroCyclicVertex) :
    PolygonSmoothing.chart (Q m) ((S).parameter m i) ≅
      PolygonSmoothing.chart (Q m) ((D).parameter m i) :=
  (S).diagonalNodeIso σ hS ha 0 hr m i

/-- Both full punctures of each actual node comparison. -/
def arithmeticZeroCyclicPunctureIso (m : ℕ) (i : ZeroCyclicVertex) (a : Bool) :
    branchTorus (Q m) ≅ branchTorus (Q m) :=
  (S).diagonalPunctureIso σ hS ha 0 hr m i a

local notation "N" => arithmeticZeroCyclicNodeIso hπ data H hj u hu
local notation "P" => arithmeticZeroCyclicPunctureIso hπ data H hj u hu

/-- Both complete boundaries are induced by the same actual whole-node isomorphism. -/
@[reassoc] theorem arithmeticZeroCyclicNodeIso_puncture
    (m : ℕ) (i : ZeroCyclicVertex) (a : Bool) :
    punctureOpen ((S).parameter m i) a ≫ (N m i).hom =
      (P m i a).hom ≫ punctureOpen ((D).parameter m i) a :=
  (S).diagonalNodeIso_puncture σ hS ha 0 hr m i a

/-- Every exact full seed edge transports to standard inversion after the node corrections. -/
@[reassoc] theorem arithmeticZeroCyclicPunctureIso_edge (m : ℕ) (i : ZeroCyclicVertex) :
    (P m i true).hom ≫ (edgeInversion (Q m)).hom =
      (punctureSpecIso ((S).edge m i)).hom ≫ (P m (σ i) false).hom :=
  (S).diagonalPunctureIso_edge σ hS ha 0 hr m i

/-- Each whole-node comparison is over the full original arithmetic base. -/
@[reassoc] theorem arithmeticZeroCyclicNodeIso_base (m : ℕ) (i : ZeroCyclicVertex) :
    (N m i).hom ≫ chartStructure (Q m) ((D).parameter m i) =
      chartStructure (Q m) ((S).parameter m i) :=
  (S).diagonalNodeIso_base σ hS ha 0 hr m i

/-- Every whole-node quotient square uses the actual seed and corrected smoothings. -/
@[reassoc] theorem arithmeticZeroCyclicNodeIso_restriction (m : ℕ) (i : ZeroCyclicVertex) :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
      ((S).parameter (m + 1) i) ((S).parameter m i) ((hS).1 m i))) ≫ (N (m + 1) i).hom =
    (N m i).hom ≫ Spec.map (CommRingCat.ofHom
      (ringMap (restriction R π m).toRingHom ((D).parameter (m + 1) i)
        ((D).parameter m i) ((arithmeticZeroCyclicDiagonal_compatible hπ data H hj u hu).1 m i))) :=
  (S).diagonalNodeIso_restriction σ hS ha 0 hr m i

end FLT.Mazur.WeierstrassDividedDepth
