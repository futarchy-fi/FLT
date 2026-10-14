/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelSourceBranch
public import FLT.Mazur.SchemeRelationSeedOrbit

/-!
# Original finite Picard inverses from source orbit seeds

A monic two-sided etale seed needs only meet every original source orbit over
the generic coefficient point. The full kernel coverage is constructed by
original relation composition, and gives genuine principal inverse patches,
a nonnilpotent coefficient witness, and a represented original source point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
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
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "m" => modelRelationKernelMap f hL d V c k (Over.Hom.left v) H
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]
  {Z : Scheme} (a : Z ⟶ A.left) [Etale a]
  [Etale (a ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (a ≫ (finiteKernelProjection f hL d V c k).left)] [Nonempty Z]

omit [Etale a] in
/-- Source orbit coverage constructs ALL generic points of the actual candidate scheme kernel. -/
theorem finiteModel_generic_image_of_orbit_seed
    (hc : ∀ x : A.left, (v).left x = genericPoint T →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z)) :
    ∀ x : K, b x = genericPoint T → x ∈ Set.range (fun r : D ↦ m r) :=
  (SchemeRelationMonicSeedKernel.generic_image_iff_orbits
    (equivalence f hL d V c k) (v).left H a).mpr hc

/-- Original orbit coverage gives actual principal inverses and the nonnilpotent coefficient. -/
theorem finiteModel_coefficient_of_orbit_seed
    (hc : ∀ x : A.left, (v).left x = genericPoint T →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z)) :
    ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ t ∈ s, ∃ e : ((K).basicOpen t).toScheme ⟶ D, e ≫ m = ((K).basicOpen t).ι) ∧
      (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  finiteModel_coefficient_of_source_branch f hL d V c k a
    (finiteModel_generic_image_of_orbit_seed f hL d V c k a hc)

/-- The constructed inverses reach the represented full ORIGINAL Picard source. -/
theorem finiteModelFppfSource_nonempty_of_orbit_seed
    (hc : ∀ x : A.left, (v).left x = genericPoint T →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z)) :
    Nonempty (modelFppfSource f hL d V c k v H).left :=
  finiteModelFppfSource_nonempty_of_source_branch f hL d V c k a
    (finiteModel_generic_image_of_orbit_seed f hL d V c k a hc)

end FLT.Mazur.HilbertChart.AffineRestriction
