/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalUniversalScaling

/-!
# Scaling on the original polygon times a variable torus

The cartesian coefficient comparison makes the constructed variable scaling
a morphism on the actual fiber product. Its unit-valued sections retain the
whole polygon, including nodes. No complete-family action is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The original polygon times the Laurent parameter over the unchanged base. -/
abbrev scalingProduct := pullback (toBase R t n h)
  (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* R[T;T⁻¹])))

/-- The coefficient-extended family is the actual full action input product. -/
def scalingProductIso : scalingParameterFamily R t n h ≅ scalingProduct R t n h :=
  parameterPullbackIso LaurentPolynomial.C t (LaurentPolynomial.C t) rfl n h

/-- The comparison retains the original polygon input. -/
@[reassoc] theorem scalingProductIso_fst :
    (scalingProductIso R t n h).hom ≫ pullback.fst _ _ =
      scalingParameterProjection R t n h :=
  parameterPullbackIso_fst _ _ _ _ _ _

/-- The comparison retains the variable torus input. -/
@[reassoc] theorem scalingProductIso_snd :
    (scalingProductIso R t n h).hom ≫ pullback.snd _ _ =
      toBase R[T;T⁻¹] (LaurentPolynomial.C t) n h :=
  parameterPullbackIso_snd _ _ _ _ _ _

/-- The whole original product has a constructed polygon-valued scaling morphism. -/
def scalingProductAction : scalingProduct R t n h ⟶ scheme R t n h :=
  (scalingProductIso R t n h).inv ≫ universalScaling R t n h

/-- The product action retains the original universal map on its full coefficient chart. -/
@[reassoc] theorem scalingProductIso_action :
    (scalingProductIso R t n h).hom ≫ scalingProductAction R t n h =
      universalScaling R t n h := by
  rw [scalingProductAction, Iso.hom_inv_id_assoc]

/-- The action is over the original base, using the actual second product projection. -/
@[reassoc] theorem scalingProductAction_base :
    scalingProductAction R t n h ≫ toBase R t n h =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom LaurentPolynomial.C) := by
  apply (cancel_epi (scalingProductIso R t n h).hom).mp
  rw [scalingProductIso_action_assoc, scalingProductIso_snd_assoc, universalScaling_base]

/-- Pair every original polygon point with a fixed coefficient-unit parameter. -/
def scalingProductSection (a : Rˣ) : scheme R t n h ⟶ scalingProduct R t n h :=
  scalingParameterSection R t n h a ≫ (scalingProductIso R t n h).hom

/-- The unit section keeps the entire original polygon as its first input. -/
@[reassoc] theorem scalingProductSection_fst (a : Rˣ) :
    scalingProductSection R t n h a ≫ pullback.fst _ _ = 𝟙 _ := by
  rw [scalingProductSection, Category.assoc, scalingProductIso_fst,
    scalingParameterSection_projection]

/-- Its second input is precisely evaluation of the Laurent variable at the chosen unit. -/
@[reassoc] theorem scalingProductSection_snd (a : Rˣ) :
    scalingProductSection R t n h a ≫ pullback.snd _ _ =
      toBase R t n h ≫ Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.eval₂ (RingHom.id R) a)) := by
  rw [scalingProductSection, Category.assoc, scalingProductIso_snd,
    scalingParameterSection, parameterProjection_base]

/-- Evaluation on the original full product gives the already constructed automorphism. -/
@[reassoc] theorem scalingProductSection_action (a : Rˣ) :
    scalingProductSection R t n h a ≫ scalingProductAction R t n h = scaling R t n h a := by
  rw [scalingProductSection, Category.assoc, scalingProductIso_action,
    scalingParameterSection_universalScaling]

/-- The actual unit-parameter section acts identically on all original points and nilpotents. -/
@[reassoc] theorem scalingProductSection_one_action :
    scalingProductSection R t n h 1 ≫ scalingProductAction R t n h = 𝟙 _ := by
  rw [scalingProductSection_action, scaling_one]

end FLT.Mazur.PolygonInfinitesimal
