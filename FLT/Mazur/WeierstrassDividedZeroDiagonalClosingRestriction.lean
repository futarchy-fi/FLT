/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalClosingComparison
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonComparisonRestriction
public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasRestriction

/-!
# Full diagonal closing unions follow the original arithmetic quotients

Restrict the original global arrow to the actual union of the retained and
terminal opens. Its whole comparison follows the independent polygon arrow.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
  arithmeticZeroDiagonalAtlasChart simultaneousTwistedArithmeticRestriction
/-- Two whole open chart images remain in the next pair under commuting quotient squares. -/
theorem openPair_quotient_le {X Y A B A' B' : Scheme}
    (f : A ⟶ X) (g : B ⟶ X) (f' : A' ⟶ Y) (g' : B' ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion f'] [IsOpenImmersion g']
    (q : X ⟶ Y) (r : A ⟶ A') (s : B ⟶ B')
    (hr : r ≫ f' = f ≫ q) (hs : s ≫ g' = g ≫ q) :
    f.opensRange ⊔ g.opensRange ≤ q ⁻¹ᵁ (f'.opensRange ⊔ g'.opensRange) := by
  rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · exact Or.inl ⟨r a, congrArg (fun h ↦ h a) hr⟩
  · exact Or.inr ⟨s b, congrArg (fun h ↦ h b) hs⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last D
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "U" => fun k ↦ arithmeticZeroDiagonalClosingUnion hπ data H k hj u hu
local notation "J" => fun k ↦ arithmeticZeroDiagonalClosingUnionIso hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroDiagonalClosingUnionMap hπ data H k hj u hu
local notation "l" => fun k b ↦ Iso.hom (edgeInversion (Q k)) ≫ leftBranchOpen (Q k) (s k b)
local notation "r" => fun k b ↦ punctureOpen (t k) b

/-- The original global quotient sends the whole closing union into the next one. -/
theorem arithmeticZeroDiagonalClosingUnion_restriction_le (b : Bool) :
    U m b ≤ q ⁻¹ᵁ U (m + 1) b := by
  exact openPair_quotient_le (c m (.retained ⟨0, by omega⟩ b)) (c m .terminal)
    (c (m + 1) (.retained ⟨0, by omega⟩ b)) (c (m + 1) .terminal)
    q (S (.retained ⟨0, by omega⟩ b)) (S .terminal)
    (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m
      (.retained ⟨0, by omega⟩ b))
    (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m .terminal)

/-- Restrict the original global quotient to each entire actual closing union. -/
def arithmeticZeroDiagonalClosingUnionRestriction (b : Bool) :
    (U m b).toScheme ⟶ (U (m + 1) b).toScheme :=
  (q).resLE _ _ (arithmeticZeroDiagonalClosingUnion_restriction_le hπ data H m hj u hu b)

local notation "ρ" => arithmeticZeroDiagonalClosingUnionRestriction hπ data H m hj u hu

/-- The complete closing-union quotient retains its original global arrow. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionRestriction_global (b : Bool) :
    ρ b ≫ (U (m + 1) b).ι = (U m b).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _

/-- The full retained chart keeps the exact corrected source coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionRestriction_retained (b : Bool) :
    (pushout.inl (l m b) (r m b) ≫ (J m b).hom) ≫ ρ b =
      S (.retained ⟨0, by omega⟩ b) ≫
        pushout.inl (l (m + 1) b) (r (m + 1) b) ≫ (J (m + 1) b).hom := by
  apply (cancel_mono (U (m + 1) b).ι).mp
  simp only [Category.assoc, arithmeticZeroDiagonalClosingUnionRestriction_global,
    arithmeticZeroDiagonalClosingUnionIso_global,
    arithmeticZeroDiagonalClosingUnionIso_global_assoc,
    arithmeticZeroDiagonalClosingToGlobal_retained,
    arithmeticZeroDiagonalClosingToGlobal_retained_assoc]
  exact (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m
    (.retained ⟨0, by omega⟩ b)).symm

/-- The common full terminal keeps its single actual corrected coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionRestriction_terminal (b : Bool) :
    (pushout.inr (l m b) (r m b) ≫ (J m b).hom) ≫ ρ b =
      S .terminal ≫ pushout.inr (l (m + 1) b) (r (m + 1) b) ≫ (J (m + 1) b).hom := by
  apply (cancel_mono (U (m + 1) b).ι).mp
  simp only [Category.assoc, arithmeticZeroDiagonalClosingUnionRestriction_global,
    arithmeticZeroDiagonalClosingUnionIso_global,
    arithmeticZeroDiagonalClosingUnionIso_global_assoc,
    arithmeticZeroDiagonalClosingToGlobal_terminal,
    arithmeticZeroDiagonalClosingToGlobal_terminal_assoc]
  exact (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m .terminal).symm

/-- Each entire closing comparison follows the original source and target quotient arrows. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionMap_restriction (b : Bool) :
    ρ b ≫ F (m + 1) b = F m b ≫
      arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu := by
  apply (cancel_epi (J m b).hom).mp
  apply pushout.hom_ext
  · have h₀ := arithmeticZeroDiagonalClosingUnionMap_retained hπ data H m hj u hu b
    have h₁ := arithmeticZeroDiagonalClosingUnionMap_retained hπ data H (m + 1) hj u hu b
    have hs := arithmeticZeroDiagonalClosingUnionRestriction_retained hπ data H m hj u hu b
    have ht := arithmeticZeroDiagonalPolygonRetainedMap_restriction hπ data H m hj u hu b
    rw [← arithmeticZeroDiagonalAtlasRestriction_last hπ data H hj u hu m b] at ht
    have he := congrArg (· ≫ F (m + 1) b) hs
    simp only [Category.assoc] at he h₀ h₁ ⊢
    rw [he, h₁, ← ht]
    simpa only [Category.assoc] using
      (congrArg (· ≫ arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu) h₀).symm
  · have h₀ := arithmeticZeroDiagonalClosingUnionMap_terminal hπ data H m hj u hu b
    have h₁ := arithmeticZeroDiagonalClosingUnionMap_terminal hπ data H (m + 1) hj u hu b
    have hs := arithmeticZeroDiagonalClosingUnionRestriction_terminal hπ data H m hj u hu b
    have ht := arithmeticZeroDiagonalPolygonTerminalChart_restriction hπ data H m hj u hu
    rw [← arithmeticZeroDiagonalAtlasRestriction_terminal hπ data H hj u hu m] at ht
    have he := congrArg (· ≫ F (m + 1) b) hs
    simp only [Category.assoc] at he h₀ h₁ ⊢
    rw [he, h₁, ← ht]
    simpa only [Category.assoc] using
      (congrArg (· ≫ arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu) h₀).symm

end FLT.Mazur.WeierstrassDividedDepth
