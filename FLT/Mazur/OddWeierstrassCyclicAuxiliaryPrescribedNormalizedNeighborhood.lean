/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalPrescribedLocalCubic
public import FLT.Mazur.OddWeierstrassCyclicLocalOriginalAuxiliary

/-!
# Normalized neighborhoods retain independent frames and prescribed generators

Over a base where three is invertible, the actual odd normalized subgroup
covers a smooth original object locally. The compatible comparison carries
the chosen universal generator to the specified original pulled generator.
The auxiliary frame comes from the original local cubic cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hP h₃ in
/-- The direct normalized chart locally retains the specified original generator. -/
theorem exists_auxiliary_prescribed_normalized_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (m : Labels 3 →* (𝟙_ (Over U) ⟶ (E.baseChange g).group)),
          Function.Injective m ∧ ∃ q : U ⟶ normalizedLocus n true,
          ∃ a : CompatibleIso ((normalizedSubgroup n true).baseChange q) (H.baseChange g),
            (∀ i, pullSection q (oddNormalizedAuxiliaryMarking n i) ≫
              a.curve.hom.group = m i) ∧
            pullSection q (oddNormalizedGenerator n) ≫ a.subgroup.hom = pullSection g P := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, J, Q, hQ, a, ha⟩ :=
    H.exists_prescribed_local_cartierCubic hP hx
  let _ := hT
  let _ := hW
  let _ := hf
  let _ := hl
  have hT₃ : IsUnit (3 : Γ(T, ⊤)) := by
    simpa only [map_ofNat] using h₃.map f.appTop.hom
  let k := (pointedCubicAuxiliaryCover W hT₃).hom
  let _ : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₃
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₃
  let p := (pointedCubicHomAuxiliaryParameter W hT₃ (J.generatorCurveMarking hQ)).left
  let hz := pointedCubicHomPrescribed_equation W hT₃ J hQ
  let q := cyclicHomNormalizedLocusPoint n p hz
  obtain ⟨t, ht⟩ := hxf
  obtain ⟨u, hu⟩ := k.surjective t
  let _ : Nonempty (pointedCubicAuxiliaryCover W hT₃).left := ⟨u⟩
  refine ⟨(pointedCubicAuxiliaryCover W hT₃).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_,
    localOriginalAuxiliaryMarking H f W hT₃ J a,
    localOriginalAuxiliaryMarking_injective H f W hT₃ J a, q,
    localActualNormalizedIso H f W hT₃ J a hQ, ?_, ?_⟩
  · exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩
  · exact localActualNormalizedIso_auxiliary H f W hT₃ J a hQ
  · exact localActualNormalizedIso_generator H f W hT₃ J a hQ ha

end FLT.Mazur.OddWeierstrassParameter
