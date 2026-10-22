/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPairedNormalizedCover
public import FLT.Mazur.SchemePairedStableAffineRefinement
public import FLT.Mazur.EquivalenceRelationNormalizedInvariantOpen

/-!
# Paired affine endpoint lifts over an original invariant open

The common affine chart lies over the prescribed invariant source domain.
Both exact endpoint equations survive, including on nonreduced coefficient
schemes. Thus the original section-ring scalar map is available on the chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B Y Z : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ) (o : Fin n)
  (j : source p q (Fin n) o ⟶ Y) [IsClosedImmersion j]
  (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z] (x y : B ⟶ A)
local instance pairDomainOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance pairDomainOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance pairDomainOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] source action

variable (E : A.Opens) (hE : p ⁻¹ᵁ E = q ⁻¹ᵁ E)
include j k hE in
/-- Every coefficient point admits actual simultaneous affine normalized endpoint lifts. -/
theorem exists_paired_affine_endpoint_lifts_within
    (hx : Set.range x ⊆ exactRank (Over.mk p) n)
    (hy : Set.range y ⊆ exactRank (Over.mk p) n) (z : B) (hxE : x z ∈ E) (hyE : y z ∈ E) :
    ∃ (U : (source p q (Fin n) o).Opens) (T : Scheme.{0})
      (a b : T ⟶ U.toScheme) (c : T ⟶ B) (t : T),
      IsAffineOpen U ∧ IsAffine T ∧ Etale c ∧ c t = z ∧
      U ≤ first p q (Fin n) o ⁻¹ᵁ E ∧
      (∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U) ∧
      a ≫ U.ι ≫ first p q (Fin n) o = c ≫ x ∧
      b ≫ U.ι ≫ first p q (Fin n) o = c ≫ y := by
  let π := pairedNormalizedProjection (p := p) (q := q) n n o o x y
  let u := pairedNormalizedFirst (p := p) (q := q) n n o o x y
  let v := pairedNormalizedSecond (p := p) (q := q) n n o o x y
  obtain ⟨w, hw⟩ := pairedNormalizedProjection_surjective n n o o x y e hx hy z
  have huE : u w ∈ first p q (Fin n) o ⁻¹ᵁ E := by
    change (u ≫ first p q (Fin n) o) w ∈ E
    rw [pairedNormalizedFirst_endpoint]
    change x (π w) ∈ E
    rwa [hw]
  have hvE : v w ∈ first p q (Fin n) o ⁻¹ᵁ E := by
    change (v ≫ first p q (Fin n) o) w ∈ E
    rw [pairedNormalizedSecond_endpoint]
    change y (π w) ∈ E
    rwa [hw]
  obtain ⟨U, W, hU, hW, hwW, hUE, he, a, b, ha, hb⟩ :=
    SchemePairedStableAffineLifts.exists_common_affine_lifts_within
      (action e (Fin n) o) j k (first p q (Fin n) o ⁻¹ᵁ E)
      (first_preimage_stable e (Fin n) o E hE) u v w huE hvE
  let _ : IsAffine W.toScheme := hW
  let _ := pairedNormalizedProjection_etale n n o o x y e
  refine ⟨U, W.toScheme, a, b, W.ι ≫ π, ⟨w, hwW⟩, hU, inferInstance,
    inferInstance, hw, hUE, he, ?_, ?_⟩
  · rw [← Category.assoc, ha, Category.assoc]
    exact congrArg (fun f ↦ W.ι ≫ f) (pairedNormalizedFirst_endpoint n n o o x y)
      |>.trans (Category.assoc _ _ _).symm
  · rw [← Category.assoc, hb, Category.assoc]
    exact congrArg (fun f ↦ W.ι ≫ f) (pairedNormalizedSecond_endpoint n n o o x y)
      |>.trans (Category.assoc _ _ _).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames
