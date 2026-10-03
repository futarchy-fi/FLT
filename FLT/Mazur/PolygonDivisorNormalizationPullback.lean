/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryDivisor
public import FLT.Mazur.PolygonNormalizationTorusPullback

/-!
# Pulling the polygon boundary ideal to normalization

The scheme-theoretic preimage of a marked section on its component is the
original marked point of P1. Every other factor is the unit ideal, so pulling
back the actual product retains exactly that one ideal.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonDivisorNormalizationPullback
open PolygonPinching PolygonMarkedSections ProjectiveLineActionSpecialization FCurve
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual unit-marked section of the projective normalization component. -/
def markedPoint (a : Kˣ) : Spec (.of K) ⟶ ProjectiveLine.scheme K :=
  unitPoint K a ≫ (torusToComponent K).left

include h in
/-- A marked point has precisely its specified scheme-theoretic preimage. -/
theorem section_square (a : Kˣ) (i : Fin n) :
    IsPullback (markedPoint K a) (𝟙 _) (componentι K n i ≫ p).left
      (sectionMap K n p a i) := by
  have H : IsPullback (𝟙 _) (unitPoint K a) (unitPoint K a) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (H.paste_vert
    (PolygonNormalizationTorusPullback.torus_square K n hn p q h i)).flip

include h in
/-- Pullback retains the marked section ideal itself, including its multiplicity. -/
theorem section_ideal (a : Kˣ) (i : Fin n) :
    (sectionMap K n p a i).ker.comap (componentι K n i ≫ p).left =
      (markedPoint K a).ker := by
  let := PolygonSeparated.cocone K n hn p q h
  let := isClosedImmersion_section C.hom _ (section_base K n p a i)
  have H := section_square K n hn p q h a i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

include h in
/-- A marked section from another component pulls back to the unit ideal. -/
theorem other_section_ideal (a : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    (sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left = ⊤ := by
  let := PolygonSeparated.cocone K n hn p q h
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change (componentι K n i ≫ p).left x ∈ (sectionMap K n p a j).ker.support ↔ False
  rw [← SetLike.mem_coe, support_section_ker C.hom _ (section_base K n p a j)]
  constructor
  · rintro ⟨z, hz⟩
    exact Set.disjoint_left.mp
      (PolygonNormalizationTorusPullback.component_torus_disjoint K n hn p q h hij)
      ⟨x, rfl⟩ (hz ▸ section_mem_torus K n p a j z)
  · exact False.elim

include h in
/-- The actual product boundary ideal restricts to exactly one marked-point ideal. -/
theorem ideal (a : Fin n → Kˣ) (i : Fin n) :
    (PolygonBoundaryDivisor.ideal K n p a).comap (componentι K n i ≫ p).left =
      (markedPoint K (a i)).ker := by
  classical
  rw [PolygonBoundaryDivisor.ideal, idealSheaf_comap_prod,
    Finset.prod_eq_single i]
  · exact section_ideal K n hn p q h (a i) i
  · intro j _ hji
    exact other_section_ideal K n hn p q h (a j) hji.symm
  · simp
end FLT.Mazur.PolygonDivisorNormalizationPullback
