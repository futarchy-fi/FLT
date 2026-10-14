/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelUnramifiedInverses
public import FLT.Mazur.AffineHilbertModelFlatFppf

/-!
# Original represented Picard regions on nonreduced flat finite models

Actual flatness of the finite coefficient projection gives the same precise
coefficient certificate for represented Picard nonemptiness on nonreduced
models. With unramified geometry, generic original-relation point coverage
constructs the represented region and a point of its complete original source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
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
local notation "m" => pullback.lift p q H
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
local instance finiteFlatPicardKernelMono : Mono m :=
  modelRelationKernelMap_mono f hL d V c k (v).left H


variable [Flat (finiteKernelProjection f hL d V c k).left]

/-- On flat finite models, represented nonemptiness needs no reduction or integral source. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_of_flat :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      Nonempty (modelEffectiveTarget f hL d V c k v H).left :=
  modelFppfTarget_nonempty_iff_of_flat f hL d V c k v H

/-- The finite original coefficient criterion now detects the represented nonreduced region. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_coefficient_of_flat :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
        (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D, a ≫ m = ((K).basicOpen t).ι) ∧
        (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r := by
  rw [finiteModelPicardFppfTarget_nonempty_iff_of_flat]
  exact finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k

/-- No nonempty effective neighborhood is lost on passage to the represented original image. -/
theorem finiteModelPicardFppfLocus_hits_of_flat
    (W : (modelEffectiveTarget f hL d V c k v H).left.Opens)
    (hW : (W : Set (modelEffectiveTarget f hL d V c k v H).left).Nonempty) :
    ((W : Set (modelEffectiveTarget f hL d V c k v H).left) ∩
      SchemeFppfTargetOpen.locus
        (modelEffectiveRelativeProjection f hL d V c k v H).left).Nonempty :=
  modelFppfLocus_inter_nonempty_of_flat f hL d V c k v H W hW

variable [FormallyUnramified (finiteKernelProjection f hL d V c k).left]
  [IrreducibleSpace (finiteKernelModel f hL d V c k).left]

/-- Generic original relation images construct represented Picard nonemptiness on flat models.
The target is only topologically irreducible and can retain nonzero nilpotents. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_generic_image_of_flat :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      ∀ x : K, b x = genericPoint T → x ∈ Set.range m := by
  rw [finiteModelPicardFppfTarget_nonempty_iff_of_flat]
  exact finiteModelEffectiveTarget_nonempty_iff_generic_image f hL d V c k

/-- Generic original arrows give an actual point of the complete represented original source. -/
theorem finiteModelPicardFppfSource_nonempty_of_generic_image_of_flat
    (hg : ∀ x : K, b x = genericPoint T → x ∈ Set.range m) :
    Nonempty (modelFppfSource f hL d V c k v H).left :=
  (modelFppfSource_nonempty_iff_of_flat f hL d V c k v H).mpr
    ((finiteModelEffectiveTarget_nonempty_iff_generic_image f hL d V c k).mpr hg)

end FLT.Mazur.HilbertChart.AffineRestriction
