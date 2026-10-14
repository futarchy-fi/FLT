/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelSourceBranchCoverage

/-!
# Finite Picard coefficient witnesses from one propagated source branch

Generic point coverage now constructs actual principal inverses and a
nonnilpotent coefficient in the original finite model. The geometric seed
is one nonempty branch etale over both original source and coefficient target.
Global flatness, global unramifiedness and integral sources are not premises.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "H" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "m" => modelRelationKernelMap f hL d V c k (Over.Hom.left v) H
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]
  {Z : Scheme} (a : Z ⟶ A.left) [Etale a]
  [Etale (a ≫ (finiteKernelProjection f hL d V c k).left)] [Nonempty Z]
include a

/-- Construct finite principal original inverses and their actual coefficient-ideal witness. -/
theorem finiteModel_coefficient_of_source_branch
    (hg : ∀ x : K, b x = genericPoint T → x ∈ Set.range (fun z : D ↦ m z)) :
    ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ t ∈ s, ∃ e : ((K).basicOpen t).toScheme ⟶ D, e ≫ m = ((K).basicOpen t).ι) ∧
      (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  (finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k).mp
    (modelEffectiveTarget_nonempty_of_source_branch f hL d V c k v a H hg)

/-- The same original seed reaches an actual represented point, including nonreduced structure. -/
theorem finiteModelFppfSource_nonempty_of_source_branch
    (hg : ∀ x : K, b x = genericPoint T → x ∈ Set.range (fun z : D ↦ m z)) :
    Nonempty (modelFppfSource f hL d V c k v H).left :=
  modelFppfSource_nonempty_of_source_branch f hL d V c k v a H hg

end FLT.Mazur.HilbertChart.AffineRestriction
