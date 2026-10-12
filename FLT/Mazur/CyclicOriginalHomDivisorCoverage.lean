/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalLocalCartierCubic
public import FLT.Mazur.PointedCubicHomRetainedSubgroup

/-!
# Original cyclic objects covered by multiplicity-preserving parameters

Every smooth original cyclic object has fppf local unrestricted parameters
whose orbit divisor is its actual subgroup under a full compatible comparison.
This includes non-etale levels. The ambient parameter scheme is not yet a
moduli chart: the subgroup condition still needs scheme-theoretic representation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (h₂ : IsUnit (2 : Γ(S, ⊤)))

include hc h₂ in
/-- Non-etale cyclic levels have local parameters retaining the entire original subgroup ideal. -/
theorem exists_original_hom_divisor_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (p : U ⟶ (cyclicHomAuxiliaryScheme n).left)
          (J : (cyclicHomSourceCurve n p).FiniteSubgroup n),
          J.ideal = cyclicHomSourceIdeal n p ∧
            (∃ P, J.IsCartierGenerator P) ∧ Nonempty (CompatibleIso J (H.baseChange g)) := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, J, P, hP, ⟨a⟩⟩ :=
    hc.exists_original_local_cartierCubic H hx
  let _ := hT
  let _ := hW
  let _ := hf
  let _ := hl
  have hT₂ : IsUnit (2 : Γ(T, ⊤)) := by
    simpa only [map_ofNat] using h₂.map f.appTop.hom
  let φ := J.generatorCurveMarking hP
  let k := (pointedCubicAuxiliaryCover W hT₂).hom
  let _ : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₂
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₂
  refine ⟨(pointedCubicAuxiliaryCover W hT₂).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_,
    (pointedCubicHomAuxiliaryParameter W hT₂ φ).left,
    pointedCubicHomRetainedSubgroup W hT₂ φ J,
    pointedCubicHomRetained_ideal W hT₂ φ J hP rfl,
    ⟨J.pullGenerator k P, pointedCubicHomRetained_generator W hT₂ φ J hP⟩,
    ⟨(pointedCubicHomRetainedIso W hT₂ φ J).symm.trans
      ((a.baseChange k).trans (compatibleBaseChangeComp H f k).symm)⟩⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
