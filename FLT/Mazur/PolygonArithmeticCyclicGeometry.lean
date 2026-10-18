/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicFactorRestriction
public import FLT.Mazur.PolygonSmoothingPunctureSpecCalculus
public import FLT.Mazur.PolygonSmoothingSpecialFiber

/-!
# Whole-node scheme comparisons for simultaneous cyclic normalization

Every diagonal comparison includes the entire seed node, both full punctures,
the original coefficient projection, and the original quotient square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized r₀)
local notation "D" => S.diagonal σ hS ha r₀ hr₀
local notation "hD" => S.diagonal_compatible σ hS ha r₀ hr₀
local notation "Q" m => Quotient R π m

/-- The actual entire seed node is isomorphic to its simultaneously normalized diagonal node. -/
def State.diagonalNodeIso (m : ℕ) (i : ι) :
    chart (Q m) (S.parameter m i) ≅ chart (Q m) ((D).parameter m i) :=
  Scheme.Spec.mapIso
    (S.iterateNodeFactor σ hS ha r₀ hr₀ m m i).toRingEquiv.toCommRingCatIso.op

/-- Both full punctures of this same whole-node comparison. -/
def State.diagonalPunctureIso (m : ℕ) (i : ι) (a : Bool) :
    branchTorus (Q m) ≅ branchTorus (Q m) :=
  punctureSpecIso (S.iteratePunctureFactor σ hS ha r₀ hr₀ m m i a)

local notation "N" => S.diagonalNodeIso σ hS ha r₀ hr₀
local notation "P" => S.diagonalPunctureIso σ hS ha r₀ hr₀

/-- Every whole-node comparison retains both complete original boundary charts. -/
@[reassoc] theorem State.diagonalNodeIso_puncture (m : ℕ) (i : ι) (a : Bool) :
    punctureOpen (S.parameter m i) a ≫ (N m i).hom =
      (P m i a).hom ≫ punctureOpen ((D).parameter m i) a :=
  punctureFactor_spec _ _ _ _ a (S.iterateNodeFactor_puncture σ hS ha r₀ hr₀ m m i a)

/-- Every full original cyclic edge transports to standard inversion simultaneously. -/
@[reassoc] theorem State.diagonalPunctureIso_edge (m : ℕ) (i : ι) :
    (P m i true).hom ≫ (edgeInversion (Q m)).hom =
      (punctureSpecIso (S.edge m i)).hom ≫ (P m (σ i) false).hom := by
  have h := S.iteratePunctureFactor_edge σ hS ha r₀ hr₀ m m i
  change ((D).edge m i).trans _ = _ at h
  rw [S.diagonal_normalized σ hS ha r₀ hr₀ m i] at h
  have h' := congrArg (fun e ↦ (punctureSpecIso e).hom) h
  simpa only [punctureSpecIso_trans, Iso.trans_hom, punctureSpecIso_invert,
    State.diagonalPunctureIso] using h'

/-- The whole comparison retains the full original coefficient projection. -/
@[reassoc] theorem State.diagonalNodeIso_base (m : ℕ) (i : ι) :
    (N m i).hom ≫ chartStructure (Q m) ((D).parameter m i) =
      chartStructure (Q m) (S.parameter m i) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact (S.iterateNodeFactor σ hS ha r₀ hr₀ m m i).commutes x

/-- The complete diagonal node comparisons retain the actual original quotient square. -/
@[reassoc] theorem State.diagonalNodeIso_restriction (m : ℕ) (i : ι) :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
      (S.parameter (m + 1) i) (S.parameter m i) (hS.1 m i))) ≫ (N (m + 1) i).hom =
      (N m i).hom ≫ Spec.map (CommRingCat.ofHom
        (ringMap (restriction R π m).toRingHom ((D).parameter (m + 1) i)
          ((D).parameter m i) ((hD).1 m i))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (S.diagonalNodeFactor_restriction σ hS ha r₀ hr₀ m i))

end FLT.Mazur.PolygonArithmeticCyclic
