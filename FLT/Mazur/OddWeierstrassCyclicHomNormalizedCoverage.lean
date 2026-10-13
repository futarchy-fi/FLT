/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomAffineNeighborhood
public import FLT.Mazur.OddWeierstrassCyclicHomAffineNormalization

/-!
# Normalized affine odd charts cover original smooth cyclic families

Normalize each affine refinement of the original fppf family. The resulting
points have normalized auxiliary coordinates, and their universal subgroups
recover the entire original subgroup, including in characteristic two.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hc h₃ in
/-- Original cyclic objects have affine normalized points with full subgroup comparisons. -/
theorem exists_affine_normalized_hom_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (R : CommRingCat) (g : Spec R ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (a : Spec R ⟶ levelThree.left)
          (q : Spec R ⟶ cyclicHomUniversalMultiplicationLocus n),
          q ≫ cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomAuxiliary n).left =
            auxiliaryFamilyNormalizedPoint a ∧
              Nonempty (CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange q)
                (H.baseChange g)) := by
  obtain ⟨R, g, hg, hl, hxg, hV, p, J, _, ⟨P, hP⟩, ⟨a⟩⟩ :=
    exists_affine_original_hom_neighborhood H hc h₃ hx
  exact ⟨R, g, hg, hl, hxg, hV, cyclicHomAuxiliaryPoint n p,
    cyclicHomAffineNormalizedLocusPoint p J hP,
    cyclicHomAffineNormalizedLocusPoint_auxiliary p J hP,
    ⟨(cyclicHomAffineNormalizedLocusIso p J hP).trans a⟩⟩

include hc h₃ in
/-- A small affine fppf cover represents every original object by normalized odd points. -/
theorem exists_normalized_hom_subgroup_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n),
      (∀ i, IsAffine (C.X i)) ∧ ∀ i,
        Nonempty (CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange (q i))
          (H.baseChange (C.f i))) ∧
        ∃ (R : CommRingCat) (e : C.X i ≅ Spec R) (a : Spec R ⟶ levelThree.left),
          q i ≫ cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomAuxiliary n).left =
            e.hom ≫ auxiliaryFamilyNormalizedPoint a := by
  have h (x : S) := exists_affine_normalized_hom_neighborhood H hc h₃
    (V := ⊤) (x := x) (by trivial)
  choose R g hg hl hx hV a q hq ha using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S
      (fun x ↦ Spec (R x)) g (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  refine ⟨C, q, fun i ↦ ?_, fun i ↦ ⟨ha i, R i, Iso.refl _, a i, ?_⟩⟩
  · change IsAffine (Spec (R i))
    infer_instance
  · exact (hq i).trans (Category.id_comp _).symm

end FLT.Mazur.OddWeierstrassParameter
