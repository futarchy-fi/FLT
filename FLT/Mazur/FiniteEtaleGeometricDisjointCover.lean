/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleGeometricSectionCover
public import FLT.Mazur.FiniteEtaleDisjointSectionNeighborhood

/-!
# Constructed disjoint finite étale section covers

Every finite étale scheme admits a complete disjoint section cover after an
affine étale neighborhood of any geometric base test. The original cartesian
square and the entire geometric map survive; a splitting is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleGeometricDisjointCover
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsFinite f] [IsAffine Y]
  {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)

/-- Every geometric test has an affine étale neighborhood with an actual disjoint full cover. -/
theorem exists_cover :
    ∃ (n : ℕ) (U E : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U)
      (h : E ⟶ X) (p : E ⟶ U) (s : Fin n → (U ⟶ E)),
      IsAffine U ∧ Etale q ∧ q.appTop.hom.FinitePresentation ∧ z ≫ q = b ∧
      IsPullback h p f q ∧ IsFinite p ∧ Etale p ∧
      (∀ i, s i ≫ p = 𝟙 U) ∧ (∀ i, IsOpenImmersion (s i)) ∧
      (∀ x : E, ∃ i, s i (p x) = x) ∧
      Pairwise (fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j))) := by
  obtain ⟨n, U, E, q, z, h, p, s, hU, hq, _, hz, H, hp, he, hs, _, hc⟩ :=
    FiniteEtaleGeometricSectionCover.exists_cover f b
  obtain ⟨W, m, r, hW, hzW, hr, hi, hc', hd⟩ :=
    FiniteEtaleDisjointSectionNeighborhood.exists_disjoint_cover p s hs hc (z default)
  have hzr : Set.range z ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change z x ∈ W
    rwa [Subsingleton.elim x (default : Spec (.of K))]
  let w := IsOpenImmersion.lift W.ι z hzr
  have hw : w ≫ W.ι = z := IsOpenImmersion.lift_fac _ _ _
  let _ : IsAffine W.toScheme := hW
  refine ⟨m, W.toScheme, (p ⁻¹ᵁ W).toScheme, W.ι ≫ q, w,
    (p ⁻¹ᵁ W).ι ≫ h, p ∣_ W, r, hW, inferInstance,
    (W.ι ≫ q).finitePresentation_appTop, ?_, ?_, inferInstance, inferInstance,
    hr, hi, hc', hd⟩
  · rw [← Category.assoc, hw, hz]
  · exact (isPullback_morphismRestrict p W).flip.paste_horiz H

end FLT.Mazur.FiniteEtaleGeometricDisjointCover
