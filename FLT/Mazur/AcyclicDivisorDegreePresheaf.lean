/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAcyclicDivisorPresheaf
public import FLT.Mazur.RelativeIdealFamilies

/-!
# The full acyclic degree-d divisor presheaf

Finite locally free degree cuts out a subfunctor of the full acyclic
divisor presheaf. Exchanging the fiber-product factors converts every
member to an actual finite flat ideal family for Hilbert classification.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve ClosedIdealCover SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (d : ℕ)

/-- The intrinsic acyclic divisors whose actual closed families have constant degree d. -/
def acyclicDivisorDegreeSubfunctor : Subfunctor (finiteTypeAcyclicDivisorPresheaf f) where
  obj T := {D | FiniteLocallyFreeDegree (D.val.val.subschemeι ≫ pullback.snd f T.unop.hom) d}
  map {T U} g D hD := by
    change FiniteLocallyFreeDegree
      ((finiteTypeAcyclicDivisorMap f g.unop D).val.val.subschemeι ≫ _) d
    rw [finiteTypeAcyclicDivisorMap_ideal]
    exact restriction_degree D.val.val _ (relativeTotalMap_isPullback f g.unop) d hD

/-- Every degree-d acyclic divisor gives an actual Hilbert family after factor exchange. -/
def acyclicDegreeHilbertFamily (T : Over (Spec (.of R)))
    (D : (acyclicDivisorDegreeSubfunctor f d).toFunctor.obj (op T)) :
    RelativeIdealFamilies f d T.hom := by
  refine ⟨D.val.val.val.comap (pullbackSymmetry f T.hom).inv, ?_⟩
  have H : IsPullback (pullbackSymmetry f T.hom).inv
      (pullback.fst T.hom f) (pullback.snd f T.hom) (𝟙 T.left) :=
    IsPullback.of_horiz_isIso ⟨by
      simp only [pullbackSymmetry_inv_comp_snd, Category.comp_id]⟩
  exact restriction_degree D.val.val.val _ H d D.property

/-- Exchanging factors back recovers the entire original acyclic divisor ideal. -/
lemma acyclicDegreeHilbertFamily_recover (T : Over (Spec (.of R)))
    (D : (acyclicDivisorDegreeSubfunctor f d).toFunctor.obj (op T)) :
    (acyclicDegreeHilbertFamily f d T D).val.comap (pullbackSymmetry f T.hom).hom =
      D.val.val.val := by
  change (D.val.val.val.comap _).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]

/-- The full family in the Hilbert convention still distinguishes every original divisor. -/
theorem acyclicDegreeHilbertFamily_injective (T : Over (Spec (.of R))) :
    Function.Injective (acyclicDegreeHilbertFamily f d T) := by
  intro D E h
  apply Subtype.ext
  apply acyclicRankOneRelativeDivisor_ext
  rw [← acyclicDegreeHilbertFamily_recover f d T D,
    ← acyclicDegreeHilbertFamily_recover f d T E, h]

end FLT.Mazur.CartierAbel
