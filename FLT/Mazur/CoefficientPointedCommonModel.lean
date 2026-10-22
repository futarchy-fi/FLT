/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianModelSection
public import FLT.Mazur.CoefficientIndependentModel
public import FLT.Mazur.CoefficientSectionEquality

/-!
# Independence of the original pointed whole-family model

Independently chosen proper finitely presented models of the same marked
family admit a common finite coefficient refinement preserving both model
markings and their actual recovery from the original section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open SectionCoverBaseChange
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Independent proper pointed models admit a common refinement retaining the marking. -/
theorem exists_independent_pointed_common_model {A : Type u} [CommRing A]
    (R S : Subalgebra ℤ A) [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y Z : Scheme.{u}} {r : X ⟶ Spec (.of A)}
    (p : Y ⟶ Spec (.of R)) (q : Z ⟶ Spec (.of S))
    [IsProper p] [IsProper q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    {a : X ⟶ Y} {b : X ⟶ Z}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hq : IsPullback b r q (Spec.map (CommRingCat.ofHom S.val.toRingHom)))
    (s : Spec (.of A) ⟶ X) (hs : s ≫ r = 𝟙 _)
    (sR : Spec (.of R) ⟶ Y) (hR : sR ≫ p = 𝟙 _)
    (sS : Spec (.of S) ⟶ Z) (hS : sS ≫ q = 𝟙 _)
    (heR : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ sR = s ≫ a)
    (heS : Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ sS = s ≫ b)
    (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (T : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ T) (_ : c₀ ⊆ T)
      (hRT : R ≤ T) (hST : S ≤ T)
      (W : Scheme.{u}) (v : W ⟶ Spec (.of T)) (u : X ⟶ W)
      (c : W ⟶ Y) (d : W ⟶ Z) (t : Spec (.of T) ⟶ W),
      IsProper v ∧ LocallyOfFinitePresentation v ∧ t ≫ v = 𝟙 _ ∧
      IsPullback c v p (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)) ∧
      IsPullback d v q (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) ∧
      IsPullback u r v (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
      u ≫ c = a ∧ u ≫ d = b ∧
      t ≫ c = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) ≫ sR ∧
      t ≫ d = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) ≫ sS ∧
      Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ t = s ≫ u := by
  obtain ⟨B, hB, hcB, hRB, hSB, W, v, u, c, d, hcp, hdq, huv, huc, hud⟩ :=
    exists_independent_coefficient_common_model R S p q hp hq c₀ hc₀
  let _ : IsProper v := MorphismProperty.of_isPullback hcp inferInstance
  let _ : LocallyOfFinitePresentation v := MorphismProperty.of_isPullback hcp inferInstance
  let tR := cartesianModelSection hcp sR hR
  let tS := cartesianModelSection hdq sS hS
  have htR := cartesianModelSection_over hcp sR hR
  have htS := cartesianModelSection_over hdq sS hS
  have heR' : Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ tR = s ≫ u := by
    apply cartesianModelSection_recovery hcp sR hR r u _ huv.w s hs
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ sR = s ≫ u ≫ c
    rw [huc, heR]
  have heS' : Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ tS = s ≫ u := by
    apply cartesianModelSection_recovery hdq sS hS r u _ huv.w s hs
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ sS = s ≫ u ≫ d
    rw [hud, heS]
  obtain ⟨i, hi⟩ := exists_coefficient_sections_eq B v tR tS htR htS
    (heR'.trans heS'.symm)
  let bi := (coefficientSpectrumToInitial B).app i
  let ti := sectionMap v bi tR htR
  have hbr : bi ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (hRB.trans i.unop.property.1)).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hbs : bi ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSB).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (hSB.trans i.unop.property.1)).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hc := (IsPullback.of_hasPullback v bi).paste_horiz hcp
  have hd := (IsPullback.of_hasPullback v bi).paste_horiz hdq
  rw [hbr] at hc
  rw [hbs] at hd
  refine ⟨i.unop.val, i.unop.property.2, fun x hx ↦ i.unop.property.1 (hcB hx),
    hRB.trans i.unop.property.1, hSB.trans i.unop.property.1, _, pullback.snd v bi,
    coefficientModelRecovery huv i, pullback.fst v bi ≫ c, pullback.fst v bi ≫ d, ti,
    inferInstance, inferInstance, sectionMap_snd v bi tR htR, hc, hd,
    coefficientModelRecovery_isPullback huv i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, coefficientModelRecovery_fst, huc]
  · rw [← Category.assoc, coefficientModelRecovery_fst, hud]
  · change (sectionMap v bi tR htR ≫ pullback.fst v bi) ≫ c = _
    rw [sectionMap_fst, Category.assoc, cartesianModelSection_projection,
      ← Category.assoc, hbr]
  · change (sectionMap v bi tR htR ≫ pullback.fst v bi) ≫ d = _
    rw [sectionMap_fst, hi, Category.assoc, cartesianModelSection_projection,
      ← Category.assoc, hbs]
  · exact coefficientSection_recovery huv s hs tR htR heR' i

end FLT.Mazur.Approximation
