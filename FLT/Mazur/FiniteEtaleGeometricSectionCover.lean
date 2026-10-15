/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteGeometricFiberSpread
public import FLT.Mazur.FiniteEtaleSectionCoverNeighborhood

/-!
# Constructed finite section covers over affine étale neighborhoods

Every finite étale scheme admits, around each geometric base test, a common
affine étale neighborhood whose ENTIRE base change is covered by finitely many
actual open sections. The original pullback square and the whole geometric
test are retained. No split fiber, section family, or degree bound is supplied.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleGeometricSectionCover
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsFinite f] [IsAffine Y]
  {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)

/-- An affine étale neighborhood has a complete finite section cover of its base change. -/
theorem exists_cover :
    ∃ (n : ℕ) (U E : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U)
      (h : E ⟶ X) (p : E ⟶ U) (s : Fin n → (U ⟶ E)),
      IsAffine U ∧ Etale q ∧ q.appTop.hom.FinitePresentation ∧ z ≫ q = b ∧
      IsPullback h p f q ∧ IsFinite p ∧ Etale p ∧
      (∀ i, s i ≫ p = 𝟙 U) ∧ (∀ i, IsOpenImmersion (s i)) ∧
      (∀ x : E, ∃ i, s i (p x) = x) := by
  obtain ⟨n, U, q, z, s, _, hq, hz, hs, _, hc⟩ :=
    EtaleFiniteGeometricFiberSpread.exists_affine_sections f b
  let p := pullback.snd f q
  obtain ⟨O, hO, hzO, hcov⟩ :=
    FiniteEtaleSectionCoverNeighborhood.exists_affine_section_cover p s hs (z default) hc
  have hr : Set.range z ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change z x ∈ O
    rwa [Subsingleton.elim x (default : Spec (.of K))]
  let w := IsOpenImmersion.lift O.ι z hr
  have hw : w ≫ O.ι = z := IsOpenImmersion.lift_fac _ _ _
  let a (i : Fin n) := FiniteEtaleSectionCoverNeighborhood.restrictedSection p (s i) (hs i) O
  have ha (i : Fin n) : a i ≫ (p ∣_ O) = 𝟙 O.toScheme :=
    FiniteEtaleSectionCoverNeighborhood.restrictedSection_section p (s i) (hs i) O
  let _ : IsAffine O.toScheme := hO
  refine ⟨n, O.toScheme, (p ⁻¹ᵁ O).toScheme, O.ι ≫ q, w,
    (p ⁻¹ᵁ O).ι ≫ pullback.fst f q, p ∣_ O, a, hO, inferInstance,
    (O.ι ≫ q).finitePresentation_appTop, ?_, ?_, inferInstance, inferInstance, ha,
    fun i ↦ UnramifiedSectionImmersion.isOpenImmersion _ _ (ha i), hcov⟩
  · rw [← Category.assoc, hw, hz]
  · exact (isPullback_morphismRestrict p O).flip.paste_horiz (IsPullback.of_hasPullback f q)

end FLT.Mazur.FiniteEtaleGeometricSectionCover
