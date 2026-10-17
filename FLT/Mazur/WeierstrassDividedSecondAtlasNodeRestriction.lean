/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondNodeRestriction
public import FLT.Mazur.WeierstrassDividedSecondJointAtlasSystem
public import FLT.Mazur.WeierstrassDividedSecondJointAtlasIncoming

/-!
# Installed second atlas restrictions are the explicit node coefficient maps

The last and predecessor identifications connect the transported restrictions
to actual coefficient maps. The terminal square keeps both previous drifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticSecondJointAtlasCorrection arithmeticSecondJointOrientedIso
  arithmeticSecondPrecedingOrientedIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticSecondJointAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticSecondJointLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticSecondJointOrientedIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- The installed last node has exactly the original normalized coefficient restriction. -/
@[reassoc] theorem arithmeticSecondJointLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) =
      ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticSecondJointAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticSecondJointAtlasCorrection_last,
    arithmeticSecondJointAtlasCorrection_last] at h
  rw [arithmeticResidualLiftAtlasRestriction_retained] at h
  have hc := congrArg (fun f ↦ f ≫ (N (m + 1) b).hom)
    (arithmeticSecondJointOrientedIso_restriction hπ data H j hj u hu m b)
  apply (cancel_epi (C m b).hom).mp
  simp only [Iso.trans_hom, Category.assoc] at h
  simp only [Category.assoc] at hc
  exact h.trans hc

variable (a : ℕ) (ha : a + 1 = j)
local notation "M" => fun k ↦
  arithmeticSecondJointPrecedingIdentification hπ data H k j hj u hu a ha
local notation "P" => fun k ↦ arithmeticSecondPrecedingOrientedIso hπ data H k j hj u hu

/-- The installed predecessor retains its full changed-smoothing coefficient restriction. -/
@[reassoc] theorem arithmeticSecondJointPrecedingIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticSecondPrecedingRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticSecondJointAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticSecondJointAtlasCorrection_preceding hπ data H m j hj u hu a ha b,
    arithmeticSecondJointAtlasCorrection_preceding hπ data H (m + 1) j hj u hu a ha b] at h
  rw [arithmeticResidualLiftAtlasRestriction_retained] at h
  have hp := congrArg (fun f ↦ f ≫ (M (m + 1) b).hom)
    (arithmeticSecondPrecedingOrientedIso_restriction hπ data H j hj u hu m b)
  apply (cancel_epi (P m b).hom).mp
  simp only [Iso.trans_hom, Category.assoc] at h
  simp only [Category.assoc] at hp
  exact h.trans hp

/-- An unaffected retained label keeps the full original normalized node. -/
def arithmeticSecondJointEarlierIdentification
    (i : Fin (j + 1)) (hi : i.val + 1 ≠ j) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m)
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m) ≅
      arithmeticSecondJointAtlasObject hπ data H m j hj u hu (.retained i b) :=
  eqToIso (by
    simp only [arithmeticSecondJointAtlasObject, hi, ↓reduceIte]
    rfl)

/-- The installed correction on an earlier retained label is only its type identification. -/
theorem arithmeticSecondJointAtlasCorrection_earlier
    (i : Fin (j + 1)) (hi : i.val + 1 ≠ j) (hl : i.val ≠ j) (b : Bool) :
    arithmeticSecondJointAtlasCorrection hπ data H m j hj u hu (.retained i b) =
      arithmeticSecondJointEarlierIdentification hπ data H j hj u hu m i hi b := by
  rw [arithmeticSecondJointAtlasCorrection]
  simp only [hi, hl, ↓reduceDIte, ↓reduceIte, Iso.refl_trans]
  rfl

/-- Every unaffected retained chart uses its original full coefficient restriction. -/
@[reassoc] theorem arithmeticSecondJointEarlierIdentification_restriction
    (i : Fin (j + 1)) (hi : i.val + 1 ≠ j) (hl : i.val ≠ j) (b : Bool) :
    (arithmeticSecondJointEarlierIdentification hπ data H j hj u hu m i hi b).hom ≫
        S m (.retained i b) =
      ρ ≫ (arithmeticSecondJointEarlierIdentification
        hπ data H j hj u hu (m + 1) i hi b).hom := by
  have h := arithmeticSecondJointAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained i b)
  dsimp only at h
  rw [arithmeticSecondJointAtlasCorrection_earlier hπ data H j hj u hu m i hi hl b,
    arithmeticSecondJointAtlasCorrection_earlier hπ data H j hj u hu (m + 1) i hi hl b,
    arithmeticResidualLiftAtlasRestriction_retained] at h
  exact h

/-- Both original full initial charts keep their original arithmetic restrictions. -/
theorem arithmeticSecondJointAtlasRestriction_initial (b : Bool) :
    S m (.initial b) =
      arithmeticLabeledAtlasRestriction hπ data H m (j + 1) hj (.initial b) := by
  simp only [arithmeticSecondJointAtlasRestriction, arithmeticSecondJointAtlasCorrection,
    arithmeticResidualLiftAtlasRestriction, arithmeticResidualLiftAtlasCorrection,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  rfl

local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu
local notation "F" => fun k ↦ arithmeticSecondResidualLiftTerminalIso hπ data H k j hj u hu

/-- The actual terminal restriction is the coefficient map on its twice corrected smoothing. -/
theorem arithmeticSecondJointAtlasRestriction_terminal :
    S m .terminal = Spec.map (CommRingCat.ofHom
      (ringMap (restriction R π m).toRingHom (t (m + 1)) (t m)
        (arithmeticSecondResidualLiftSmoothing_restriction hπ data H j hj u hu m))) := by
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [arithmeticSecondJointAtlasRestriction, arithmeticSecondJointAtlasCorrection]
  change ((F m).inv ≫
    arithmeticResidualLiftAtlasRestriction hπ data H j hj u hu m .terminal ≫
      (F (m + 1)).hom) ≫ (F (m + 1)).inv = _
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    arithmeticResidualLiftAtlasRestriction_terminal]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (arithmeticSecondResidualLiftTerminalFactor_restriction hπ data H j hj u hu m).symm)

end FLT.Mazur.WeierstrassDividedDepth
