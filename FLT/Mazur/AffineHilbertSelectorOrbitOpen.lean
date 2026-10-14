/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertSelectorQuotient
public import FLT.Mazur.AffineHilbertNestedKernel

/-!
# Full saturated original open models from constructed selector seeds

An invariant arrow family on a nested Hilbert selection constructs the full
seed model. Orbit propagation and descent then produce a quotient on a genuine
saturated open of the original parameter source. No seed kernel is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] {B : Over (Spec (.of R))} (s : B ⟶ A)
  [Etale s.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d V c (s ≫ k)
local notation "q'" => snd f hL d V c (s ≫ k)
variable (r : B.left ⟶ (relation f hL d V c (s ≫ k)).left)

omit [Etale V.hom] [IsOpenImmersion k.left] [Etale s.left] in
/-- The constructed seed model has the FULL two-coordinate original restricted kernel. -/
theorem selectorSeed_isPullback (hr : r ≫ (p').left = 𝟙 B.left)
    (hi : (p').left ≫ r ≫ (q').left = (q').left ≫ r ≫ (q').left) :
    IsPullback (SchemeRelationRestriction.fst (p).left (q).left s.left)
      (SchemeRelationRestriction.snd (p).left (q).left s.left)
      (selectorProjection f hL d V c (s ≫ k) r hr hi).left
      (selectorProjection f hL d V c (s ≫ k) r hr hi).left := by
  apply (selectorProjection_isPullback f hL d V c (s ≫ k) r hr hi).of_iso
    (nestedSchemeDoubleIso f hL d V c k s) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (nestedSchemeDoubleIso_fst f hL d V c k s).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (nestedSchemeDoubleIso_snd f hL d V c k s).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The effective quotient on the genuine saturated original source open. -/
def selectorOrbitOpenProjection (hr : r ≫ (p').left = 𝟙 B.left)
    (hi : (p').left ≫ r ≫ (q').left = (q').left ≫ r ≫ (q').left) :
    (originalOrbitOpenSource f hL d V c k s.left).left ⟶
      (selectorTarget f hL d V c (s ≫ k) r).left :=
  originalOrbitOpenModel f hL d V c k s.left
    (selectorProjection f hL d V c (s ≫ k) r hr hi).left
    (selectorSeed_isPullback f hL d V c k s r hr hi)

local notation "l" => originalOrbitOpenParameter f hL d V c k s.left

/-- The rebuilt original Picard relation on the open is the complete constructed kernel. -/
theorem selectorOrbitOpenProjection_isPullback (hr : r ≫ (p').left = 𝟙 B.left)
    (hi : (p').left ≫ r ≫ (q').left = (q').left ≫ r ≫ (q').left) :
    IsPullback (fst f hL d V c l).left (snd f hL d V c l).left
      (selectorOrbitOpenProjection f hL d V c k s r hr hi)
      (selectorOrbitOpenProjection f hL d V c k s r hr hi) :=
  originalOrbitOpenModel_isPullback f hL d V c k s.left
    (selectorProjection f hL d V c (s ≫ k) r hr hi).left
    (selectorSeed_isPullback f hL d V c k s r hr hi)

/-- The actual original-open quotient is an etale surjection. -/
theorem selectorOrbitOpenProjection_cover [IsOpenImmersion (s ≫ k).left]
    (hr : r ≫ (p').left = 𝟙 B.left)
    (hi : (p').left ≫ r ≫ (q').left = (q').left ≫ r ≫ (q').left) :
    Etale (selectorOrbitOpenProjection f hL d V c k s r hr hi) ∧
      Surjective (selectorOrbitOpenProjection f hL d V c k s r hr hi) := by
  obtain ⟨he, hs⟩ := selectorProjection_cover f hL d V c (s ≫ k) r hr hi
  let _ := he
  let _ := hs
  exact originalOrbitOpenModel_cover f hL d V c k s.left
    (selectorProjection f hL d V c (s ≫ k) r hr hi).left
    (selectorSeed_isPullback f hL d V c k s r hr hi)

/-- The scheme quotient retains the ORIGINAL proper-family ground morphism. -/
@[reassoc]
theorem selectorOrbitOpenProjection_ground (hr : r ≫ (p').left = 𝟙 B.left)
    (hi : (p').left ≫ r ≫ (q').left = (q').left ≫ r ≫ (q').left) :
    selectorOrbitOpenProjection f hL d V c k s r hr hi ≫
      (selectorTarget f hL d V c (s ≫ k) r).hom =
        (originalOrbitOpenSource f hL d V c k s.left).hom := by
  apply originalOrbitOpenModel_ground f hL d V c k s.left
    (selectorProjection f hL d V c (s ≫ k) r hr hi).left
    (selectorSeed_isPullback f hL d V c k s r hr hi)
  exact (selectorProjection f hL d V c (s ≫ k) r hr hi).w.trans s.w.symm

end FLT.Mazur.HilbertChart.AffineRestriction
