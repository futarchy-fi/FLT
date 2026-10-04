/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCartierGenerator

/-!
# Transport of Cartier generators

Compatible isomorphisms of the curve and subgroup transport the actual
Cartier ideal and generator. This permits comparisons of iterated pullbacks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}

/-- Transporting a closed subscheme across an isomorphism pulls its ideal back by the inverse. -/
theorem ker_comp_iso {D X Y : Scheme} (f : D ⟶ X) [IsClosedImmersion f] (e : X ≅ Y) :
    (f ≫ e.hom).ker = f.ker.comap e.inv := by
  have q : IsPullback (f ≫ e.hom) (𝟙 D) e.inv f :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  rw [← q.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

variable (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n) (c : E ≅ F)
  (d : H.carrier ≅ J.carrier) [IsMonHom d.hom]
  (hd : H.curveMap ≫ c.hom.curve = d.hom ≫ J.curveMap)

omit [IsMonHom d.hom] in
include hd in
/-- Compatible isomorphisms identify the subgroup ideals on the whole curves. -/
theorem ideal_transport : J.ideal = H.ideal.comap c.inv.curve.left := by
  have : IsIso d.hom.left := inferInstanceAs (IsIso ((Over.forget S).map d.hom))
  rw [ideal, ← Scheme.Hom.ker_comp_of_isIso d.hom.left]
  change (d.hom ≫ J.curveMap).left.ker = _
  rw [← hd]
  exact ker_comp_iso H.curveMap.left ((Over.forget S).mapIso (curveIso c))

include hd in
/-- The image of a Cartier generator under compatible isomorphisms is again a generator. -/
theorem IsCartierGenerator.transport {P : 𝟙_ (Over S) ⟶ H.carrier}
    (hP : H.IsCartierGenerator P) : J.IsCartierGenerator (P ≫ d.hom) := by
  have : IsProper E.curve.hom := E.family.family.1
  have : IsIso c.inv.curve.left :=
    inferInstanceAs (IsIso ((forgetCurve ⋙ Over.forget S).map c.inv))
  refine ⟨?_, ?_, ?_⟩
  · rw [← MonObj.pow_comp, hP.1, MonObj.one_comp]
  · rw [ideal_transport H J c d hd]
    simpa only [Over.w] using hP.2.1.comap_of_isOpenImmersion c.inv.curve.left
  · rw [ideal_transport H J c d hd, hP.2.2, FCurve.idealSheaf_comap_prod]
    apply Finset.prod_congr rfl
    intro i _
    have : IsClosedImmersion ((P ^ i.val) ≫ H.curveMap).left :=
      FCurve.isClosedImmersion_section E.curve.hom _ (((P ^ i.val) ≫ H.curveMap).w)
    rw [← MonObj.pow_comp, Category.assoc, ← hd, ← Category.assoc]
    exact (ker_comp_iso (((P ^ i.val) ≫ H.curveMap).left)
      ((Over.forget S).mapIso (curveIso c))).symm

include hd in
/-- Existence of a Cartier generator is invariant under compatible isomorphisms. -/
theorem exists_generator_iff :
    (∃ P, H.IsCartierGenerator P) ↔ ∃ Q, J.IsCartierGenerator Q := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P ≫ d.hom, hP.transport H J c d hd⟩
  · rintro ⟨Q, hQ⟩
    have he : J.curveMap ≫ c.inv.curve = d.inv ≫ H.curveMap := by
      have : IsIso c.hom.curve := inferInstanceAs (IsIso (forgetCurve.map c.hom))
      apply (cancel_mono c.hom.curve).mp
      have hc : c.inv.curve ≫ c.hom.curve = 𝟙 F.curve :=
        congrArg Hom.curve c.inv_hom_id
      simp only [Category.assoc, hc, Category.comp_id]
      rw [hd, ← Category.assoc, d.inv_hom_id, Category.id_comp]
    have : IsMonHom d.symm.hom := inferInstanceAs (IsMonHom d.inv)
    exact ⟨Q ≫ d.inv, hQ.transport J H c.symm d.symm he⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
