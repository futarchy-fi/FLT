/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCyclicLevel
public import FLT.Mazur.FiniteSubgroupClassPresheaf

/-!
# The presheaf of ample cyclic levels

Take compatible-isomorphism classes of the actual ample cyclic levels.
Canonical geometric pullback comparisons prove the presheaf laws. Forgetting
the level conditions embeds this presheaf into all finite-subgroup classes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-- Isomorphism classes of generalized curves with an ample cyclic subgroup of rank n. -/
def ampleCyclicClasses (S : Scheme) (n : ℕ) := Quotient (ampleCyclicLevelSetoid S n)

/-- Actual base change on ample cyclic isomorphism classes. -/
def ampleCyclicClassesPullback {S T : Scheme} (g : T ⟶ S) (n : ℕ) :
    ampleCyclicClasses S n → ampleCyclicClasses T n :=
  Quotient.map (ampleCyclicLevelsPullback g n)
    (fun _ _ h ↦ ampleCyclicLevelsPullback_rel g n h)

/-- Identity base change preserves each ample cyclic class. -/
theorem ampleCyclicClassesPullback_id (S : Scheme) (n : ℕ) :
    ampleCyclicClassesPullback (𝟙 S) n = id := by
  funext x
  refine Quotient.inductionOn x fun a ↦ ?_
  exact Quotient.sound ⟨compatibleBaseChangeId a.val.2⟩

/-- Iterated base change agrees with restriction along the composite. -/
theorem ampleCyclicClassesPullback_comp {S T U : Scheme}
    (g : T ⟶ S) (h : U ⟶ T) (n : ℕ) :
    ampleCyclicClassesPullback (h ≫ g) n =
      ampleCyclicClassesPullback h n ∘ ampleCyclicClassesPullback g n := by
  funext x
  refine Quotient.inductionOn x fun a ↦ ?_
  exact Quotient.sound ⟨compatibleBaseChangeComp a.val.2 g h⟩

/-- The moduli presheaf imposing both the ample and cyclic conditions. -/
def ampleCyclicClassPresheaf (n : ℕ) : Schemeᵒᵖ ⥤ Type 1 where
  obj S := ampleCyclicClasses S.unop n
  map f := ↾(ampleCyclicClassesPullback f.unop n)
  map_id S := by
    ext x
    exact congrFun (ampleCyclicClassesPullback_id S.unop n) x
  map_comp f g := by
    ext x
    exact congrFun (ampleCyclicClassesPullback_comp f.unop g.unop n) x

/-- Forget the proved ample and cyclic predicates while retaining the geometric class. -/
def ampleCyclicClassesForget (S : Scheme) (n : ℕ) :
    ampleCyclicClasses S n → finiteSubgroupClasses S n :=
  Quotient.map Subtype.val (fun _ _ h ↦ h)

/-- Forgetting conditions does not identify any additional geometric classes. -/
theorem ampleCyclicClassesForget_injective (S : Scheme) (n : ℕ) :
    Function.Injective (ampleCyclicClassesForget S n) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun a b h ↦ ?_
  change Quotient.mk (compatibleIsoSetoid S n) a.val =
    Quotient.mk (compatibleIsoSetoid S n) b.val at h
  apply Quotient.sound
  change (compatibleIsoSetoid S n).r a.val b.val
  exact Quotient.exact h

/-- Forgetting conditions commutes with arbitrary base change. -/
theorem ampleCyclicClassesForget_pullback {S T : Scheme} (g : T ⟶ S) (n : ℕ)
    (x : ampleCyclicClasses S n) :
    ampleCyclicClassesForget T n (ampleCyclicClassesPullback g n x) =
      finiteSubgroupClassesPullback g n (ampleCyclicClassesForget S n x) := by
  refine Quotient.inductionOn x fun _ ↦ ?_
  rfl

/-- The ample cyclic moduli presheaf maps naturally into all finite-subgroup classes. -/
def ampleCyclicClassForget (n : ℕ) :
    ampleCyclicClassPresheaf n ⟶ finiteSubgroupClassPresheaf n where
  app S := ↾(ampleCyclicClassesForget S.unop n)
  naturality _ _ f := by
    ext x
    exact ampleCyclicClassesForget_pullback f.unop n x

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
