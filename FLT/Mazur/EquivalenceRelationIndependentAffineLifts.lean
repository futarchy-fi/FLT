/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPairedNormalizedCover
public import FLT.Mazur.EquivalenceRelationNormalizedInvariantOpen
public import FLT.Mazur.SchemeIndependentStableAffineLifts

/-!
# Affine normalized lifts at independent endpoint ranks

Each endpoint uses its own exact rank and stable affine chart. The common
etale coefficient neighborhood retains both morphisms and the prescribed
original invariant domain, without requiring an original relation arrow.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B Y Z Y' Z' : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
  (n m : ℕ) (o : Fin n) (o' : Fin m)
  (j : source p q (Fin n) o ⟶ Y) [IsClosedImmersion j]
  (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z]
  (j' : source p q (Fin m) o' ⟶ Y') [IsClosedImmersion j']
  (k' : Y' ⟶ Z') [IsOpenImmersion k'] [IsAffine Z'] (x y : B ⟶ A)
local instance independentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance independentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance independentOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] source action

variable (E : A.Opens) (hE : p ⁻¹ᵁ E = q ⁻¹ᵁ E)
include j k j' k' hE in
/-- Independent ranks suffice for actual affine endpoint lifts over the original domain. -/
theorem exists_independent_affine_endpoint_lifts
    (hx : Set.range x ⊆ exactRank (Over.mk p) n)
    (hy : Set.range y ⊆ exactRank (Over.mk p) m) (z : B) (hxE : x z ∈ E) (hyE : y z ∈ E) :
    ∃ (U : (source p q (Fin n) o).Opens) (V : (source p q (Fin m) o').Opens)
      (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ V.toScheme) (c : T ⟶ B) (t : T),
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffine T ∧ Etale c ∧ c t = z ∧
      U ≤ first p q (Fin n) o ⁻¹ᵁ E ∧ V ≤ first p q (Fin m) o' ⁻¹ᵁ E ∧
      (∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U) ∧
      (∀ g : Equiv.Perm (Fin m), (action e (Fin m) o' g).hom ⁻¹ᵁ V = V) ∧
      a ≫ U.ι ≫ first p q (Fin n) o = c ≫ x ∧
      b ≫ V.ι ≫ first p q (Fin m) o' = c ≫ y := by
  let π := pairedNormalizedProjection (p := p) (q := q) n m o o' x y
  let u := pairedNormalizedFirst (p := p) (q := q) n m o o' x y
  let v := pairedNormalizedSecond (p := p) (q := q) n m o o' x y
  obtain ⟨w, hw⟩ := pairedNormalizedProjection_surjective n m o o' x y e hx hy z
  have huE : u w ∈ first p q (Fin n) o ⁻¹ᵁ E := by
    change (u ≫ first p q (Fin n) o) w ∈ E
    rw [pairedNormalizedFirst_endpoint]
    change x (π w) ∈ E
    rwa [hw]
  have hvE : v w ∈ first p q (Fin m) o' ⁻¹ᵁ E := by
    change (v ≫ first p q (Fin m) o') w ∈ E
    rw [pairedNormalizedSecond_endpoint]
    change y (π w) ∈ E
    rwa [hw]
  obtain ⟨U, V, W, hU, hV, hW, hwW, hUE, hVE, hρ, hτ, a, b, ha, hb⟩ :=
    SchemeIndependentStableAffineLifts.exists_affine_lifts
      (action e (Fin n) o) (action e (Fin m) o') j k j' k'
      (first p q (Fin n) o ⁻¹ᵁ E) (first p q (Fin m) o' ⁻¹ᵁ E)
      (first_preimage_stable e (Fin n) o E hE)
      (first_preimage_stable e (Fin m) o' E hE) u v w huE hvE
  let _ : IsAffine W.toScheme := hW
  let _ := pairedNormalizedProjection_etale n m o o' x y e
  refine ⟨U, V, W.toScheme, a, b, W.ι ≫ π, ⟨w, hwW⟩, hU, hV, inferInstance,
    inferInstance, hw, hUE, hVE, hρ, hτ, ?_, ?_⟩
  · rw [← Category.assoc, ha, Category.assoc]
    exact congrArg (fun f ↦ W.ι ≫ f) (pairedNormalizedFirst_endpoint n m o o' x y)
      |>.trans (Category.assoc _ _ _).symm
  · rw [← Category.assoc, hb, Category.assoc]
    exact congrArg (fun f ↦ W.ι ≫ f) (pairedNormalizedSecond_endpoint n m o o' x y)
      |>.trans (Category.assoc _ _ _).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames
