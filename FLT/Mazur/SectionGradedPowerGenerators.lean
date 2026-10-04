/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPowers
public import FLT.Mazur.TensorPowerGeneratorOpen

/-!
# Generators represented by homogeneous ring powers

The actual section representing a ring power generates wherever the original
section does. This includes degree zero and allows scalar cancellation on
all subopens of a generator chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedPowerGenerators
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules)

/-- The section representing the `n`th ring power of a degree `d` section. -/
def powerSection (d : ℕ) (s : Piece L ⊤ d) (n : ℕ) : Piece L ⊤ (d * n) :=
  (tensorPowerMulIso L d n).hom.app ⊤ (tensorPowerSection (tensorPower L d) ⊤ s n)

/-- Inserting a power section gives exactly the power in the graded ring. -/
lemma of_powerSection (d : ℕ) (s : Piece L ⊤ d) (n : ℕ) :
    of L ⊤ (d * n) (powerSection L d s n) = (of L ⊤ d s) ^ n :=
  SectionGradedPowers.of_tensorPower L ⊤ d s n

/-- Positive ring powers have exactly the original generator open. -/
lemma generatorOpen_powerSection (hL : LocallyFreeRankOne L) (d : ℕ)
    (s : Piece L ⊤ d) {n : ℕ} (hn : 0 < n) :
    sectionGeneratorOpen (tensorPower L (d * n)) (powerSection L d s n) =
      sectionGeneratorOpen (tensorPower L d) s :=
  (sectionGeneratorOpen_iso (tensorPowerMulIso L d n) _).trans
    (tensorPowerSection_generatorOpen (hL.tensorPower d) s hn)

/-- Even the zeroth power generates on every subopen of the original generator chart. -/
lemma le_generatorOpen_powerSection (hL : LocallyFreeRankOne L) (d : ℕ)
    (s : Piece L ⊤ d) (n : ℕ) :
    sectionGeneratorOpen (tensorPower L d) s ≤
      sectionGeneratorOpen (tensorPower L (d * n)) (powerSection L d s n) := by
  cases n with
  | zero =>
    change sectionGeneratorOpen (tensorPower L d) s ≤
      sectionGeneratorOpen (structureModule X) (1 : Γ(X, ⊤))
    rw [sectionGeneratorOpen_structure, X.basicOpen_one]
    exact le_top
  | succ n => rw [generatorOpen_powerSection L hL d s (Nat.succ_pos n)]

/-- Scalar multiplication by a homogeneous power is injective on its generator chart. -/
lemma smul_powerSection_injective (hL : LocallyFreeRankOne L) (d : ℕ)
    (s : Piece L ⊤ d) (n : ℕ) (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    Function.Injective (fun a : Γ(X, U) ↦ a •
      (tensorPower L (d * n)).presheaf.map U.leTop.op (powerSection L d s n)) := by
  let := sectionGeneratorOpen_app_isIso (tensorPower L (d * n))
    (powerSection L d s n) U (hU.trans (le_generatorOpen_powerSection L hL d s n))
  exact (ConcreteCategory.bijective_of_isIso
    ((globalSectionHom _ (powerSection L d s n)).app U)).injective

end FLT.Mazur.SectionGradedPowerGenerators
