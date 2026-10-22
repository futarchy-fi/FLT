/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientPointedCommonModel
public import FLT.Mazur.CartesianMarkingLineComparison

/-!
# Common finite models retaining canonical Cartier marking lines

Independent proper pointed models with Cartier markings admit one finite
coefficient refinement. The marking is still Cartier, and both original
canonical line comparisons preserve their vanishing sections. Every pole
power is retained along both model comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.Approximation
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Independent marked coefficient models have a common canonical Cartier-line refinement. -/
theorem exists_independent_cartier_common_model {A : Type} [CommRing A]
    (R S : Subalgebra ℤ A) [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y Z : Scheme} {r : X ⟶ Spec (.of A)}
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
    (hI : EffectiveCartier sR.ker) (hJ : EffectiveCartier sS.ker)
    (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (T : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ T) (_ : c₀ ⊆ T)
      (hRT : R ≤ T) (hST : S ≤ T)
      (W : Scheme) (v : W ⟶ Spec (.of T)) (u : X ⟶ W)
      (c : W ⟶ Y) (d : W ⟶ Z) (t : Spec (.of T) ⟶ W),
      IsProper v ∧ LocallyOfFinitePresentation v ∧ t ≫ v = 𝟙 _ ∧
      IsPullback c v p (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)) ∧
      IsPullback d v q (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) ∧
      IsPullback u r v (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
      u ≫ c = a ∧ u ≫ d = b ∧
      t ≫ c = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) ≫ sR ∧
      t ≫ d = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) ≫ sS ∧
      Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ t = s ≫ u ∧
      ∃ hK : RelativeEffectiveCartier v t.ker,
        ∃ (ec : (pullback c).obj (divisorLineBundle sR.ker hI) ≅ divisorLineBundle t.ker hK.1)
          (ed : (pullback d).obj (divisorLineBundle sS.ker hJ) ≅ divisorLineBundle t.ker hK.1),
          DivisorLineSectionCompatible c hI hK.1 ec ∧
          DivisorLineSectionCompatible d hJ hK.1 ed ∧
          ∀ m : ℕ,
            Nonempty ((pullback c).obj (tensorPower (divisorLineBundle sR.ker hI) m) ≅
              tensorPower (divisorLineBundle t.ker hK.1) m) ∧
            Nonempty ((pullback d).obj (tensorPower (divisorLineBundle sS.ker hJ) m) ≅
              tensorPower (divisorLineBundle t.ker hK.1) m) := by
  obtain ⟨T, hT, hcT, hRT, hST, W, v, u, c, d, t, hv, hvfp, ht,
    hc, hd, hu, huc, hud, htc, htd, he⟩ :=
    exists_independent_pointed_common_model R S p q hp hq s hs sR hR sS hS heR heS c₀ hc₀
  have hK : RelativeEffectiveCartier v t.ker :=
    ⟨sectionPoint_cartier_baseChange hc sR t hR ht htc hI, flat_sectionImage v t ht⟩
  refine ⟨T, hT, hcT, hRT, hST, W, v, u, c, d, t, hv, hvfp, ht,
    hc, hd, hu, huc, hud, htc, htd, he, hK,
    sectionPointLineIso hc sR t hR ht htc hI hK.1,
    sectionPointLineIso hd sS t hS ht htd hJ hK.1,
    sectionPointLineIso_compatible hc sR t hR ht htc hI hK.1,
    sectionPointLineIso_compatible hd sS t hS ht htd hJ hK.1, fun m ↦ ?_⟩
  exact ⟨⟨sectionPointPowerIso hc sR t hR ht htc hI hK.1 m⟩,
    ⟨sectionPointPowerIso hd sS t hS ht htd hJ hK.1 m⟩⟩

end FLT.Mazur.Approximation
