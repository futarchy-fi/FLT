/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalPrescribedLocalCubic
public import FLT.Mazur.PointedCubicActualNormalizedGenerator

/-!
# Normalized neighborhoods retain a prescribed original Cartier generator

Over a base where two is invertible, the actual even normalized subgroup
covers a smooth original object locally. The compatible comparison carries
the chosen universal generator to the specified original pulled generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass CyclicCharacteristicAtlas GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include hP h₂ in
/-- The direct normalized chart locally retains the specified original generator. -/
theorem exists_prescribed_normalized_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ q : U ⟶ normalizedLocus n false,
          ∃ a : CompatibleIso ((normalizedSubgroup n false).baseChange q) (H.baseChange g),
            pullSection q (evenNormalizedGenerator n) ≫ a.subgroup.hom = pullSection g P := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, J, Q, hQ, a, ha⟩ :=
    H.exists_prescribed_local_cartierCubic hP hx
  let _ := hT
  let _ := hW
  let _ := hf
  let _ := hl
  have hT₂ : IsUnit (2 : Γ(T, ⊤)) := by
    simpa only [map_ofNat] using h₂.map f.appTop.hom
  let k := (pointedCubicAuxiliaryCover W hT₂).hom
  let _ : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₂
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₂
  let p := (pointedCubicHomAuxiliaryParameter W hT₂ (J.generatorCurveMarking hQ)).left
  let hz := pointedCubicHomPrescribed_equation W hT₂ J hQ
  let q := cyclicHomNormalizedLocusPoint n p hz
  let b := pointedCubicActualNormalizedIso W hT₂ J hQ
  refine ⟨(pointedCubicAuxiliaryCover W hT₂).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_, q,
    b.trans ((a.baseChange k).trans (compatibleBaseChangeComp H f k).symm), ?_⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩
  · change _ ≫ (b.subgroup.hom ≫ (a.baseChange k).subgroup.hom ≫
      (compatibleBaseChangeComp H f k).subgroup.inv) = _
    rw [← Category.assoc, pointedCubicActualNormalizedIso_generator,
      ← Category.assoc, a.baseChange_section k Q (pullSection f P) ha]
    exact compatibleBaseChangeComp_inv_section H f k P

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
