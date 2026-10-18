/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteGeometry
public import FLT.Mazur.WeierstrassDividedOneFiniteRestriction
public import FLT.Mazur.WeierstrassDividedFifthInitialNodeRestriction

/-!
# Coefficient squares for the finite depth-one geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The initial node and the two retained nodes have normalized coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (k m : ℕ)
local notation "P" => fun l ↦ arithmeticOneFiniteRetainedIso hπ data H k l hj u hu
local notation "E" => fun l ↦ arithmeticOneFiniteInitialNodeIso hπ data H k l hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticOneFiniteState hπ data H hj u hu k)
local notation "t" => PolygonArithmeticRetainedChain.State.initial
  (arithmeticOneFiniteState hπ data H hj u hu k)

/-- The exact retained seed coefficient map, before further corrections. -/
def arithmeticOneSeedRetainedRestriction (i : Fin 2) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m)
        ((arithmeticOneSeedState hπ data H hj u hu).retained m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1))
        ((arithmeticOneSeedState hπ data H hj u hu).retained (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneSeedState_compatible hπ data H hj u hu).2.1 m i b)))

/-- The new retained node's explicit coefficient restriction. -/
def arithmeticOneFiniteRetainedRestriction (i : Fin 2) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneFiniteState_compatible hπ data H hj u hu k).2.1 m i b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticOneFiniteInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneFiniteState_compatible hπ data H hj u hu k).1 m b)))

/-- Both old and new retained node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticOneFiniteRetainedIso_restriction (i : Fin 2) (b : Bool) :
    arithmeticOneSeedRetainedRestriction hπ data H hj u hu m i b ≫ (P (m + 1) i b).hom =
      (P m i b).hom ≫ arithmeticOneFiniteRetainedRestriction hπ data H hj u hu k m i b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticOneFiniteRetainedFactor_restriction hπ data H hj u hu k m i b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticOneFiniteInitialNodeIso_restriction (b : Bool) :
    arithmeticFifthInitialNodeRestriction hπ data H 1 hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticOneFiniteInitialNodeRestriction hπ data H hj u hu k m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticOneFiniteInitialFactor_restriction hπ data H hj u hu k m b)

local notation "t₀" => arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu
local notation "T" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticOneFiniteState hπ data H hj u hu k)
local notation "F" => fun l ↦ arithmeticOneFiniteTerminalIso hπ data H k l hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticOneFiniteTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneFiniteState_compatible hπ data H hj u hu k).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticOneFiniteTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 1 hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticOneFiniteTerminalRestriction hπ data H hj u hu k m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticOneFiniteTerminalFactor_restriction hπ data H hj u hu k m)).symm

end FLT.Mazur.WeierstrassDividedDepth
