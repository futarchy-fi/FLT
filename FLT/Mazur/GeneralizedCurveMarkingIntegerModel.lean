/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSmoothMarking
public import FLT.Mazur.ProperPointedLineSheafDescent

/-!+# Integer models of the original marked whole family

Over an arbitrary ring the whole proper family, its original marking and
each specified pole line descend together to finite integer coefficients.
The model is Noetherian and the section is closed. Flatness and classified
geometric fibers of the model are separate descent obligations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open Approximation FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original marked whole curve and its pole line have an actual Noetherian model. -/
theorem exists_smoothMarking_integer_model {A : Type} [CommRing A]
    (E : GeneralizedEllipticCurve (Spec (.of A)))
    (s : 𝟙_ (Over (Spec (.of A))) ⟶ E.group) (m : ℕ)
    (c : Set A) (hc : c.Finite) :
    ∃ R : Subalgebra ℤ A, Algebra.FiniteType ℤ R ∧ c ⊆ R ∧
      ∃ (Y : Scheme) (q : Y ⟶ Spec (.of R)) (M : Y.Modules),
        IsNoetherian Y ∧ IsProper q ∧ LocallyOfFinitePresentation q ∧
        LocallyFreeRankOne M ∧
        ∃ (t : Spec (.of R) ⟶ Y) (f : E.curve.left ⟶ Y),
          IsClosedImmersion t ∧ t ≫ q = 𝟙 _ ∧
          IsPullback f E.curve.hom q (Spec.map (CommRingCat.ofHom R.val.toRingHom)) ∧
          Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = (s ≫ E.inclusion).left ≫ f ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ E.smoothMarkingPower s m) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  obtain ⟨R, hR, hcR, Y, q, M, hq, hfp, hM, t, f, ht, hf, hs, hL⟩ :=
    exists_proper_pointed_line_sheaf_descent E.curve.hom (s ≫ E.inclusion).left
      (s ≫ E.inclusion).w (E.smoothMarkingPower s m)
      (E.smoothMarkingPower_rankOne s m) c hc
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have htclosed : IsClosedImmersion t := by
    have : IsClosedImmersion (t ≫ q) := by rw [ht]; infer_instance
    exact IsClosedImmersion.of_comp t q
  exact ⟨R, hR, hcR, Y, q, M, ⟨⟩, hq, hfp, hM, t, f,
    htclosed, ht, hf, hs, hL⟩

end FLT.Mazur.GeneralizedEllipticCurve
