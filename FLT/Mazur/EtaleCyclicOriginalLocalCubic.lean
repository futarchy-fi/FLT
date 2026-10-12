/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveLocalCyclicCubic
public import FLT.Mazur.EtaleCyclicSubgroupLocalPresentation

/-!
# Local cubic presentations of original smooth etale cyclic objects

Faithful markings are constructed from cyclicity and etaleness of the original
subgroup. At every original base point, an affine flat finitely presented chart
retains the actual subgroup through a full compatible DR isomorphism. The map
to the original base is the flattened composite of the generator and cubic covers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve WeierstrassIntegralChart UniversallyDistinctSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hH : H.IsCyclic)

include hH in
/-- Every original smooth etale cyclic object has actual local faithful cubic presentations. -/
theorem IsCyclic.exists_original_local_cubic {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (f : T ⟶ S),
      Flat f ∧ LocallyOfFinitePresentation f ∧ x ∈ Set.range f ∧ Set.range f ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)) (_ : W.IsElliptic)
          (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over T) ⟶ (pointedCubicFamily W).group))
          (hψ : UniversallyDistinct (fun i : ZMod n ↦ ψ (.ofAdd i))),
          Nonempty (CompatibleIso ((pointedCubicFamily W).relativeCyclicSubgroup ψ hψ)
            (H.baseChange f)) := by
  obtain ⟨U, g, hf, hs, hl, φ, hφ, ⟨a⟩⟩ := hH.exists_marked_presentation H
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
  obtain ⟨T, hT, k, hk, hyk, hV, W, hW, _, _, _, ψ, hψ, ⟨b⟩, _⟩ :=
    exists_original_local_cyclicCubic E' φ hφ (H.baseChange g) a hyS hyV
  let _ := hk
  refine ⟨T, hT, k ≫ g, inferInstance, inferInstance, ?_, ?_, W, hW, ψ, hψ,
    ⟨b.trans (compatibleBaseChangeComp H g k).symm⟩⟩
  · obtain ⟨z, hz⟩ := hyk
    exact ⟨z, by change g (k z) = x; rw [hz, hy]⟩
  · rintro _ ⟨z, rfl⟩
    exact hV ⟨z, rfl⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
