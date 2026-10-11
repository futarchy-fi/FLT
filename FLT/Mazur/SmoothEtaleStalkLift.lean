/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSmoothEtaleCoordinates
public import FLT.Mazur.EtalePolynomialStalkLift

/-!
# Étale neighborhoods through rational points at arbitrary residue primes

For a smooth scheme over an affine base, a point over a field with a stalk-surjective
base map extends to an actual étale base neighborhood. Both the original
scheme point and its base map are retained as equalities of morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothEtaleStalkLift
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] {X : Scheme}

/-- A stalk-surjective smooth field point extends to a constructed étale base neighborhood. -/
theorem exists_lift (f : X ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* K) (hφ : φ.SurjectiveOnStalks) (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom φ)) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ X) (z : Spec (.of K) ⟶ E),
      Etale e ∧ v ≫ f = e ∧ z ≫ e = Spec.map (CommRingCat.ofHom φ) ∧ z ≫ v = x := by
  obtain ⟨A, n, g, j, hg, hj, hy, hf⟩ :=
    AffineSmoothEtaleCoordinates.exists_chart f (x (IsLocalRing.closedPoint K))
  let _ := hj
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    simpa only [Subsingleton.elim w (IsLocalRing.closedPoint K)] using hy
  let a := IsOpenImmersion.lift j x hr
  have ha : a ≫ j = x := IsOpenImmersion.lift_fac j x hr
  obtain ⟨q, hq⟩ := Spec.map_surjective a
  have hbase : Spec.map q ≫ Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) =
        Spec.map (CommRingCat.ofHom φ) := by
    rw [hq, ← hf, ← Category.assoc, ha, hx]
  have hring : q.hom.comp (g.comp MvPolynomial.C) = φ := by
    rw [← Spec.map_comp, ← Spec.map_comp] at hbase
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hbase)
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ :=
    EtalePolynomialStalkLift.exists_lift g hg q.hom φ hφ hring
  refine ⟨E, e, v ≫ j, z, he, ?_, hz, ?_⟩
  · rw [Category.assoc, hf, ← Spec.map_comp]
    exact hv
  · rw [← Category.assoc, hvz]
    exact (congrArg (fun k ↦ k ≫ j) hq).trans ha

/-- The neighborhood gives a section of the actual base-changed smooth source through the point. -/
theorem exists_section (f : X ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* K) (hφ : φ.SurjectiveOnStalks) (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom φ)) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (z : Spec (.of K) ⟶ E)
      (s : E ⟶ pullback f e),
      Etale e ∧ s ≫ pullback.snd f e = 𝟙 E ∧
        z ≫ e = Spec.map (CommRingCat.ofHom φ) ∧ z ≫ s ≫ pullback.fst f e = x := by
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ := exists_lift f φ hφ x hx
  refine ⟨E, e, z, pullback.lift v (𝟙 E) (by simpa only [Category.id_comp] using hv),
    he, pullback.lift_snd _ _ _, hz, ?_⟩
  rw [pullback.lift_fst, hvz]

/-- Rational points over any base residue field have an actual étale local section. -/
theorem exists_residue_section (f : X ⟶ Spec (.of R)) [Smooth f]
    (p : Ideal R) [p.IsPrime] (x : Spec (.of p.ResidueField) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (z : Spec (.of p.ResidueField) ⟶ E)
      (s : E ⟶ pullback f e),
      Etale e ∧ s ≫ pullback.snd f e = 𝟙 E ∧
        z ≫ e = Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)) ∧
          z ≫ s ≫ pullback.fst f e = x :=
  exists_section f _ p.surjectiveOnStalks_residueField x hx

end FLT.Mazur.SmoothEtaleStalkLift
