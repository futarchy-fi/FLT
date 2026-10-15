/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalSchemeDetectingOpen
public import FLT.Mazur.SmoothGeometricOpenEtaleLift

/-!
# Original smooth étale lifts selected inside detecting opens

Smooth lifting chooses the algebraic point inside the uniform detecting
condition. This avoids prescribing a possibly inseparable original point.
Every conjugate of the selected lift satisfies the unchanged K-open family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalSmoothDetectingEtaleLift
set_option backward.isDefEq.respectTransparency false
variable {R k L K : Type} [CommRing R] [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L] {V X Y : Scheme}

/-- The original étale test is selected so its entire extended orbit meets every actual open. -/
theorem exists_lift (f : V ⟶ Spec (.of R)) [Smooth f]
    (t : Spec (.of k) ⟶ Spec (.of R)) (x : X ⟶ V) (g : X ⟶ Spec (.of k))
    (H₀ : IsPullback x g f t) [GeometricallyIntegral g]
    (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
    (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) g)
    {J : Type*} [Finite J] (U : J → Y.Opens) (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of L) ⟶ E) (q : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y)),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ t ∧
      (∀ σ, q σ ≫ a = 𝟙 _) ∧
      (∀ σ, q σ ≫ b ≫ x = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z ≫ v) ∧
      ∀ σ j, Set.range (q σ) ⊆ U j := by
  let cL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let Z := pullback g cL
  let d : Z ⟶ X := pullback.fst g cL
  let c : Z ⟶ Spec (.of L) := pullback.snd g cL
  have G := IsPullback.of_hasPullback g cL
  obtain ⟨D, j, hj, hn, hall⟩ := OriginalSchemeDetectingOpen.exists_detecting_open
    g a b H c d G.flip U hU
  let _ : IsOpenImmersion j := hj
  obtain ⟨E, e, v, z, u, hE, he, hv, hz, hu, huv⟩ :=
    SmoothGeometricOpenEtaleLift.exists_lift f (cL ≫ t) (d ≫ x) c
      (G.paste_horiz H₀) j hn
  obtain ⟨q, hq, hqb, hqU⟩ := hall u hu
  refine ⟨E, e, v, z, q, hE, he, hv, hz, hq, fun σ ↦ ?_, hqU⟩
  rw [← Category.assoc, hqb σ]
  simp only [Category.assoc] at huv ⊢
  rw [huv]

end FLT.Mazur.OriginalSmoothDetectingEtaleLift
