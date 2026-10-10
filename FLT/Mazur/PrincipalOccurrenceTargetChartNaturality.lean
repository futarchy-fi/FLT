/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceTargetChartGluing

/-!
# Naturality of the glued target-chart morphisms

Refinement commutes with each concrete patch route. The covering property
then proves the full transition square for the glued target-chart maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport

universe u v w z z' z''

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))




variable {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
  (hxy : x ≤ y) (hy : ∀ i k, Function.Bijective (y.hom i k))
  {j : κ} (i : ι)

/-- Every selected patch route commutes with its actual ambient chart transition. -/
@[reassoc] theorem principalOccurrenceTargetPatchMap_natural
    (p : PrincipalOccurrencePatchTo (dst := dst) j i) :
    principalOccurrencePatchTransition hxy hx hy p.1 ≫
        principalOccurrenceTargetPatchMap e x hx i p =
      principalOccurrenceTargetPatchMap e y hy i p ≫
        principalOccurrenceAmbientTransition hxy i := by
  simp only [principalOccurrenceTargetPatchMap, principalOccurrencePatchTransition_other_assoc,
    principalOccurrenceOpenAt_transition e x hx hxy hy, Category.assoc]

variable
  (hcx : (⨆ p : PrincipalOccurrencePatchTo (dst := dst) j i,
    (principalOccurrencePatchOpen x hx p.1).opensRange) = ⊤)
  (hcy : (⨆ p : PrincipalOccurrencePatchTo (dst := dst) j i,
    (principalOccurrencePatchOpen y hy p.1).opensRange) = ⊤)
  (hex : ∀ p q : PrincipalOccurrencePatchTo (dst := dst) j i,
    principalOccurrenceCrossOuterLeft x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i p.2.val p.2.property =
      principalOccurrenceCrossOuterRight x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i q.2.val q.2.property)
  (hey : ∀ p q : PrincipalOccurrencePatchTo (dst := dst) j i,
    principalOccurrenceCrossOuterLeft y hy p.1 q.1 ≫
        principalOccurrenceOpenAt e y hy i p.2.val p.2.property =
      principalOccurrenceCrossOuterRight y hy p.1 q.1 ≫
        principalOccurrenceOpenAt e y hy i q.2.val q.2.property)

attribute [local irreducible] principalOccurrenceTargetChartGlue principalOccurrenceTargetPatchMap

/-- The glued target-chart maps retain the entire occurrence transition square. -/
@[reassoc] theorem principalOccurrenceTargetChartGlue_natural :
    principalOccurrenceOverlapTransition hxy j ≫
        principalOccurrenceTargetChartGlue e x hx i hcx hex =
      principalOccurrenceTargetChartGlue e y hy i hcy hey ≫
        principalOccurrenceAmbientTransition hxy i := by
  apply principalOccurrencePatchSubfamily_hom_ext y hy
    (fun p : PrincipalOccurrencePatchTo (dst := dst) j i ↦ p.1) hcy
  intro p
  rw [← principalOccurrencePatchTransition_fac_assoc hxy hx hy p.1,
    principalOccurrenceTargetChartGlue_fac, principalOccurrenceTargetChartGlue_fac_assoc]
  exact principalOccurrenceTargetPatchMap_natural e x hx hxy hy i p

end FLT.Mazur.FiniteTypeRelationModel
