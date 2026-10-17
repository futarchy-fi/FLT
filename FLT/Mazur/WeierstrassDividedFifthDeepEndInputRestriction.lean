/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndIdentification
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasRestriction

/-!
# Concrete old coefficient maps at the endpoints of the fifth chain

The last and earlier sources retain their full normalized coefficient maps.
The terminal source retains every fourth smoothing correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasCorrection arithmeticFourthLastOrientedIso
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "E" => fun k ↦ arithmeticFourthOuterAtlasCorrection hπ data H k j hj u hu
local notation "S" => arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticFourthOuterLastIdentification hπ data H k j hj u hu
local notation "N₃" => fun k ↦ arithmeticThirdLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthLastOrientedIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- The last fourth input factor keeps its exact original third source. -/
theorem arithmeticFifthDeepLastInput_correction (b : Bool) :
    E m (.retained ⟨j, by omega⟩ b) = (N₃ m b).symm ≪≫ C m b ≪≫ N m b := by
  simp only [arithmeticFourthOuterAtlasCorrection, show ¬j + 2 = j by omega,
    show ¬j + 3 = j by omega, ↓reduceDIte, arithmeticFourthInitialAtlasCorrection_last,
    arithmeticFourthOuterLastIdentification, arithmeticFourthOuterUnchangedIdentification,
    Iso.trans_assoc]

/-- The last input retains its complete normalized coefficient quotient. -/
@[reassoc] theorem arithmeticFifthDeepLastInput_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthOuterAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  have h₀ := arithmeticFifthDeepLastInput_correction hπ data H j hj u hu m b
  have h₁ := arithmeticFifthDeepLastInput_correction hπ data H j hj u hu (m + 1) b
  dsimp only at h₀ h₁
  rw [h₀, h₁] at h
  have hh := congrArg (fun f ↦ (N₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdLastIdentification_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthLastOrientedIso_restriction_assoc]
  exact hh

/-- The terminal source keeps the full fourth changing-smoothing coefficient map. -/
theorem arithmeticFifthDeepTerminalInput_restriction :
    S m .terminal = arithmeticFourthTerminalRestriction hπ data H j hj u hu m := by
  simpa only [arithmeticFourthOuterAtlasRestriction, arithmeticFourthOuterAtlasCorrection,
    arithmeticFourthInitialAtlasCorrection, arithmeticFourthAtlasRestriction] using
    arithmeticFourthAtlasRestriction_terminal hπ data H j hj u hu m

variable (a : ℕ) (ha : a + 4 = j)
local notation "D" => fun k ↦
  arithmeticFifthDeepEarlierInputIdentification hπ data H k j hj u hu a ha
local notation "D₃" => fun k ↦ arithmeticThirdUnchangedIdentification hπ data H k j hj u hu

/-- The unchanged earlier input comes from the same full third normalized label. -/
@[reassoc] theorem arithmeticFifthDeepEarlierInput_correction (b : Bool) :
    (D₃ m ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫
      (E m (.retained ⟨a, by omega⟩ b)).hom = (D m b).hom := by
  simp only [arithmeticFourthOuterAtlasCorrection, arithmeticFourthInitialAtlasCorrection,
    arithmeticFourthAtlasCorrection, arithmeticFifthDeepEarlierInputIdentification,
    show ¬a = j by omega, show ¬a + 1 = j by omega,
    show ¬a + 2 = j by omega, show ¬a + 3 = j by omega,
    show ¬(j = 1 ∧ a = 0) by omega, ↓reduceDIte, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, eqToIso.hom, eqToHom_trans]

/-- The earlier input has exactly the original normalized coefficient quotient. -/
@[reassoc] theorem arithmeticFifthDeepEarlierInput_restriction (b : Bool) :
    (D m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) = ρ ≫ (D (m + 1) b).hom := by
  rw [← arithmeticFifthDeepEarlierInput_correction hπ data H j hj u hu m a ha b,
    Category.assoc, arithmeticFourthOuterAtlasCorrection_restriction,
    ← Category.assoc, arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdUnchangedIdentification_restriction, Category.assoc,
    arithmeticFifthDeepEarlierInput_correction hπ data H j hj u hu (m + 1) a ha b]

end FLT.Mazur.WeierstrassDividedDepth
