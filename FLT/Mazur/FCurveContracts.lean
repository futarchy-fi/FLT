/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPoints
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Topology.KrullDimension

/-!
# Source contracts for curve foundations

These propositions specify tasks, not proofs of their conclusions. The source ledger,
consumer mapping and representation gates are in `docs/FCURVE_CONTRACTS.md`.
Cartier divisors are expressed through actual quasi-coherent ideal sheaf data.
Relative genus and line-bundle ampleness still require the interfaces recorded there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

/-- The morphism properties underlying a proper flat family of curves.
Fiber dimension and genus are separate conditions. -/
def ProperFlatFamily {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsProper f ∧ Flat f ∧ LocallyOfFinitePresentation f

/-- Dimension one on every geometric fiber, including nonemptiness. -/
def GeometricFiberDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
    topologicalKrullDim ↥(pullback f s : Scheme.{u}) = 1

/-- Base change of the proper flat finitely presented core of a family. -/
def ProperFlatBaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Prop :=
  ProperFlatFamily f → ProperFlatFamily (pullback.snd f g)

/-- Local equations for an effective Cartier divisor, Stacks 01WS.
The generator is required only near each point, not on every affine open. -/
def EffectiveCartier {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∃ a : Γ(X, U), IsRegular a ∧ I.ideal U = Ideal.span {a}

/-- Relative effective Cartier means that the divisor itself is flat over the base. -/
def RelativeEffectiveCartier {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) : Prop :=
  EffectiveCartier I ∧ Flat (I.subschemeι ≫ f)

/-- Addition of relative divisors is multiplication of their ideal sheaves. -/
def RelativeCartierSum {X S : Scheme.{u}} (f : X ⟶ S)
    (I J : X.IdealSheafData) : Prop :=
  RelativeEffectiveCartier f I → RelativeEffectiveCartier f J →
    RelativeEffectiveCartier f (I * J)

/-- Arbitrary base change of a relative effective Cartier divisor, Stacks 056Q. -/
def RelativeCartierBaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) : Prop :=
  RelativeEffectiveCartier f I →
    RelativeEffectiveCartier (pullback.snd f g) (I.comap (pullback.fst f g))

/-- A section of a smooth separated relative curve defines a relative Cartier divisor. -/
def SmoothSectionCartier {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) : Prop :=
  SmoothOfRelativeDimension 1 f → IsSeparated f → s ≫ f = 𝟙 S →
    RelativeEffectiveCartier f s.ker

/-- The section-divisor statement on a smooth open of a possibly singular family. -/
def SmoothOpenSectionCartier {U X S : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ S)
    (s : S ⟶ U) : Prop :=
  IsOpenImmersion j → SmoothOfRelativeDimension 1 (j ≫ f) → IsSeparated f →
    s ≫ j ≫ f = 𝟙 S → RelativeEffectiveCartier f (s ≫ j).ker

/-- Finite locally free of constant degree, using Mathlib's rank function. -/
def FiniteLocallyFreeDegree {D S : Scheme.{u}} (f : D ⟶ S) (n : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ ∀ s, f.finrank s = n

/-- Rank and the three morphism properties persist under arbitrary base change. -/
def DegreeBaseChange {D S T : Scheme.{u}} (f : D ⟶ S) (g : T ⟶ S) (n : ℕ) : Prop :=
  FiniteLocallyFreeDegree f n → FiniteLocallyFreeDegree (pullback.snd f g) n

/-- The support condition used for an ample subgroup on a polygon fiber.
Its comparison with line-bundle ampleness is a separate construction gate. -/
def MeetsEveryComponent {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ C ∈ irreducibleComponents X, (C ∩ (I.support : Set X)).Nonempty

/-- The dimension bridge needed before applying the proper-curve finite-map lemma. -/
def SmoothCurveDimension {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) : Prop :=
  SmoothOfRelativeDimension 1 f → Nonempty X → topologicalKrullDim X = 1

/-- The topological step for closed fibers of an integral curve. -/
def ProperClosedSubsetFinite (X : Type u) [TopologicalSpace X] : Prop :=
  NoetherianSpace X → T0Space X → IrreducibleSpace X → topologicalKrullDim X ≤ 1 →
    ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite

/-- The integral-source case of Stacks 0CCL; the target need not be a curve. -/
def NonconstantProperCurveFinite {K : Type u} [Field K]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (y : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) : Prop :=
  IsProper x → IsIntegral X → topologicalKrullDim X ≤ 1 → IsSeparated y →
    f ≫ y = x → (∃ a b : X, f a ≠ f b) → IsFinite f

/-- Distinct images of rational sections give distinct underlying image points. -/
def DistinctSectionImages {K : Type u} [Field K]
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    (a b : Sections X) : Prop :=
  a ≫ f ≠ b ≫ f → ∃ x y : X.left, f.left x ≠ f.left y

/-- Finite scheme morphisms have finite fibers on rational sections over any field. -/
def FiniteRationalFibers {K : Type u} [Field K]
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left → ∀ y : Sections Y, Finite {x : Sections X // x ≫ f = y}

end FLT.Mazur.FCurve
