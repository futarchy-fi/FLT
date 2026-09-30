/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowSimultaneousSerreVanishing
public import FLT.Mazur.ChowWitnessCoherence
public import FLT.Mazur.RelativeDirectImageForgetting

/-!
# The Chow acyclic direct-image comparisons

Choose one actual power from simultaneous relative Serre vanishing along the
Chow modification and its composite with the structure morphism. This gives
the module higher-image and field-linear cohomology comparisons in the second
application of Leray in Stacks, Tag 02O5 (using Tag 01F6).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Scheme.Modules FLT.Mazur.FCurve

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- One exponent, chosen from the proved simultaneous Serre theorem. -/
def chowAcyclicExponent : ℕ :=
  (exists_graphLineBundlePower_simultaneously_acyclic f).choose

/-- The chosen power is acyclic along both maps, without additional hypotheses. -/
theorem chowAcyclicExponent_spec :
    ModulePushforwardAcyclic (graphClosureπ f)
        (graphLineBundlePower f (chowAcyclicExponent f)) ∧
      ModulePushforwardAcyclic (graphClosureπ f ≫ f)
        (graphLineBundlePower f (chowAcyclicExponent f)) :=
  (exists_graphLineBundlePower_simultaneously_acyclic f).choose_spec

/-- The actual coherent Chow coefficient at the single chosen exponent. -/
def chowAcyclicWitness : X.Modules := graphPowerPushforward f (chowAcyclicExponent f)

/-- The chosen direct image is coherent by the geometric Chow coherence theorem. -/
theorem chowAcyclicWitness_isFinitePresentation :
    (chowAcyclicWitness f).IsFinitePresentation :=
  chowPushforwardPower_isFinitePresentation f (chowAcyclicExponent f)

/-- Leray comparison of actual module higher direct images in every degree. -/
def chowHigherImageIso (q : ℕ) :
    ((pushforward f).rightDerived q).obj (chowAcyclicWitness f) ≅
      ((pushforward (graphClosureπ f ≫ f)).rightDerived q).obj
        (graphLineBundlePower f (chowAcyclicExponent f)) :=
  RelativeDirectImageComposition.moduleIso (graphClosureπ f) f _
    (chowAcyclicExponent_spec f).1 q

/-- Forgetting the Chow module comparison recovers the sheafified open comparison. -/
lemma chowHigherImageIso_hom_forget (q : ℕ) :
    (CoherentDevissage.moduleToSheaf (Spec (.of k))).map (chowHigherImageIso f q).hom =
      (RelativeDirectImageComposition.forgottenIso (graphClosureπ f) f
        (graphLineBundlePower f (chowAcyclicExponent f))
        (chowAcyclicExponent_spec f).1 q).hom :=
  RelativeDirectImageForgetting.moduleIso_hom_forget _ _ _ _ q

/-- The absolute comparison retains the given field structure in all degrees. -/
def chowScalarHEquiv (q : ℕ) :
    ModuleScalarH f (chowAcyclicWitness f) q ≃ₗ[k]
      ModuleScalarH (graphClosureπ f ≫ f)
        (graphLineBundlePower f (chowAcyclicExponent f)) q :=
  acyclicPushforwardScalarHEquiv (graphClosureπ f) _ (chowAcyclicExponent_spec f).1 f q

end FLT.Mazur.Chow
