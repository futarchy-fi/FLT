/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperConnectedReducedSections
public import FLT.Mazur.SchemePointedFiberSections

/-!
# Global functions at points in the same geometric fiber

Connected reduced proper fibers have no nonconstant global functions once a
rational point is specified. Two points above the same field-valued base point
therefore agree on all functions, by lifting them to the actual fiber product.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.SchemeConnectedFiberSections
variable {X S : Scheme} (f : X ⟶ S) [IsProper f]
  [GeometricallyConnected f] [GeometricallyReduced f]
variable {K : Type} [Field K]

/-- Field-valued points above the same base point agree on every global function. -/
lemma appTop_eq_of_same_fiber (a b : Spec (.of K) ⟶ X) (hab : a ≫ f = b ≫ f) :
    a.appTop = b.appTop := by
  let c := a ≫ f
  let P := pullback f c
  let p : P ⟶ X := pullback.fst f c
  let q : P ⟶ Spec (.of K) := pullback.snd f c
  let a' : Spec (.of K) ⟶ P := pullback.lift a (𝟙 _) (by simp [c])
  let b' : Spec (.of K) ⟶ P := pullback.lift b (𝟙 _) (by simpa [c] using hab.symm)
  let _ : IsReduced P :=
    GeometricallyReduced.geometrically_isReduced (f := f) c _ _ (.of_hasPullback _ _)
  let _ : ConnectedSpace P :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) c _ _ (.of_hasPullback _ _)
  have ha : a' ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hb : b' ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have H := FCurve.constantGlobalSections_of_proper_connected_reduced_section q a' ha
  have hsurj : Function.Surjective q.appTop := by
    intro r
    obtain ⟨k, hk⟩ := H.2 r
    exact ⟨(Scheme.ΓSpecIso (.of K)).inv k, hk⟩
  have : Epi q.appTop := ConcreteCategory.epi_of_surjective _ hsurj
  have he : a'.appTop = b'.appTop := by
    rw [← cancel_epi q.appTop, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, ha, hb]
  have ha' : a' ≫ p = a := pullback.lift_fst _ _ _
  have hb' : b' ≫ p = b := pullback.lift_fst _ _ _
  rw [← ha', ← hb', Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, he]
/-- A pointed family with connected reduced geometric fibers has constant fiber functions. -/
lemma pointedFiber_constantSections (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (a : Spec (.of K) ⟶ S) : FCurve.HasConstantGlobalSections (pullback.snd f a) := by
  let _ : IsReduced (pullback f a) :=
    GeometricallyReduced.geometrically_isReduced (f := f) a _ _ (.of_hasPullback _ _)
  let _ : ConnectedSpace ↥(pullback f a) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) a _ _ (.of_hasPullback _ _)
  exact FCurve.constantGlobalSections_of_proper_connected_reduced_section _
    (SchemeProperGeometricFiberSections.baseChangedSection f s hs a)
    (SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs a)

end FLT.Mazur.SchemeConnectedFiberSections
