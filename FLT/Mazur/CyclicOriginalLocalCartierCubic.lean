/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicCartierMarking
public import FLT.Mazur.GeneralizedCurveDirectLocalFamily
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Local pointed cubics retain non-etale cyclic subgroups

Use the original fppf Cartier-generator cover, then an affine cubic
neighborhood. The original carrier, full curve and Cartier multiplicities
survive both base changes and the pointed cubic comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve WeierstrassIntegralChart GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} (H : E.FiniteSubgroup n) (hH : H.IsCyclic)

include hH in
/-- Every smooth cyclic object has local Cartier-marked cubics, including non-etale levels. -/
theorem IsCyclic.exists_original_local_cartierCubic {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (f : T ⟶ S),
      Flat f ∧ LocallyOfFinitePresentation f ∧ x ∈ Set.range f ∧ Set.range f ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)) (_ : W.IsElliptic)
          (J : (pointedCubicFamily W).FiniteSubgroup n) (P : 𝟙_ (Over T) ⟶ J.carrier),
          J.IsCartierGenerator P ∧ Nonempty (CompatibleIso J (H.baseChange f)) := by
  obtain ⟨U, g, hf, hs, hl, P, hP⟩ := hH
  let _ := hf
  let _ := hs
  let _ := hl
  let _ := LocallyOfFiniteType.isLocallyNoetherian g
  let E' := E.baseChange g
  let _ : Smooth E'.curve.hom :=
    inferInstanceAs (Smooth (pullback.snd E.curve.hom g))
  let _ : IsProper E'.curve.hom := E'.family.family.1
  obtain ⟨y, hy⟩ := g.surjective x
  have hyV : y ∈ g ⁻¹ᵁ V := by change g y ∈ V; rwa [hy]
  have hyS : y ∈ smoothBaseOpen E' := by
    apply (mem_properSmoothBaseLocus E'.curve.hom y).mpr
    intro z _
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  obtain ⟨T, hT, k, hk, hyk, hV, W, hW, e, he, hz, _⟩ :=
    exists_original_local_cubicFamily E' hyS hyV
  let _ := hT
  let _ := hk
  let _ := hW
  let _ := isLocallyNoetherian_of_isOpenImmersion k
  have hz' : (E'.baseChange k).identitySection.left ≫ e.hom =
      T.toSpecΓ ≫ integralCurveZero W := by
    rw [← pullSection_identity]
    exact hz
  let J := (H.baseChange g).baseChange k
  refine ⟨T, hT, k ≫ g, inferInstance, inferInstance, ?_, ?_, W, hW,
    J.pointedCubicSubgroup W e he hz', (H.baseChange g).pullGenerator k P,
    J.pointedCubicSubgroup_generator W e he hz' (hP.baseChange _ k),
    ⟨(J.pointedCubicSubgroupIso W e he hz').symm.trans
      (compatibleBaseChangeComp H g k).symm⟩⟩
  · obtain ⟨z, hz⟩ := hyk
    exact ⟨z, by change g (k z) = x; rw [hz, hy]⟩
  · rintro _ ⟨z, rfl⟩
    exact hV ⟨z, rfl⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
