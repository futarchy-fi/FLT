/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralH1Equivalence
public import FLT.LocalClassFieldTheory.RationalCoefficientSequence

/-!
# Trivial-action H1 consists of continuous characters

Principal cocycles vanish for the actual trivial action. Thus the splitting
quotient and the integral continuous complex both recover continuous characters.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G A : Type} [Group G] [AddCommGroup A]
  [TopologicalSpace G] [TopologicalSpace A]

attribute [local instance] trivialCoefficientAction

/-- A character is a crossed homomorphism for the trivial action. -/
def characterCocycle (χ : G →ₜ* Multiplicative A) : ContinuousCocycle G A :=
  ⟨⟨fun g => (χ g).toAdd, χ.continuous⟩, fun g h => by
    exact (congrArg Multiplicative.toAdd (map_mul χ g h)).trans (add_comm _ _)⟩

/-- Every trivial-action cocycle is a continuous character. -/
def cocycleCharacter (c : ContinuousCocycle G A) : G →ₜ* Multiplicative A where
  toFun g := Multiplicative.ofAdd (c.val g)
  map_one' := by
    have h := c.property 1 1
    change c.val (1 * 1) = c.val 1 + c.val 1 at h
    change c.val 1 = 0
    exact add_left_cancel (show c.val 1 + c.val 1 = c.val 1 + 0 by simpa using h.symm)
  map_mul' g h := by
    change c.val (g * h) = c.val g + c.val h
    exact (c.property g h).trans (add_comm _ _)
  continuous_toFun := c.val.continuous

omit [TopologicalSpace G] [TopologicalSpace A] in
/-- Trivial-action principal cocycles are zero. -/
theorem trivial_principal_zero (a : A) (g : G) : g • a - a = 0 := sub_self a

/-- No two distinct trivial-action cocycles become equal in the splitting quotient. -/
theorem trivial_splittingEquivalent_iff (c d : ContinuousCocycle G A) :
    SplittingEquivalent (fun g => c.val g) (fun g => d.val g) ↔ c = d := by
  constructor
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    ext g
    have h := congrFun ha g
    simpa only [changeSplitting, trivial_principal_zero, add_zero] using h.symm
  · rintro rfl
    exact ⟨0, (changeSplitting_zero _).symm⟩

/-- The explicit H1 quotient is exactly the space of continuous characters. -/
def trivialClassCharacterEquiv : ContinuousClass G A ≃ (G →ₜ* Multiplicative A) where
  toFun := Quotient.lift cocycleCharacter (fun c d h =>
    congrArg cocycleCharacter ((trivial_splittingEquivalent_iff c d).mp h))
  invFun χ := continuousClassMk (characterCocycle χ)
  left_inv x := by
    induction x using Quotient.inductionOn with | h c =>
      apply congrArg continuousClassMk
      rfl
  right_inv χ := by ext g; rfl

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [DiscreteTopology A]

local instance trivialIntComm : SMulCommClass G ℤ A := ⟨fun _ _ _ => rfl⟩
local instance trivialContinuous : ContinuousSMul G A := ⟨continuous_snd⟩

/-- H1 of the actual continuous integral complex equals continuous characters. -/
def trivialH1CharacterEquiv : continuousCohomology ℤ G A 1 ≃ (G →ₜ* Multiplicative A) :=
  (integralH1Equiv (k := ℤ)).symm.trans trivialClassCharacterEquiv

/-- The character description evaluates the actual cohomology class as expected. -/
theorem trivialH1CharacterEquiv_class (χ : G →ₜ* Multiplicative A) :
    trivialH1CharacterEquiv (integralH1Class (k := ℤ) (characterCocycle χ)) = χ := by
  change trivialClassCharacterEquiv
    ((integralH1Equiv (k := ℤ)).symm
      (integralH1Equiv (continuousClassMk (characterCocycle χ)))) = χ
  rw [Equiv.symm_apply_apply]
  exact trivialClassCharacterEquiv.apply_symm_apply χ

end LocalClassFieldTheory
