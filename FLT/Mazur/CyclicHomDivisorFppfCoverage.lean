/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalHomDivisorCoverage
public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension

/-!
# Fppf families retaining non-etale orbit divisors

The local original comparisons give an actual small fppf cover for smooth
families, and neighborhoods on the smooth base locus of general families.
No modular map from the whole ambient parameter scheme is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include hc h₂

/-- Smooth cyclic objects have small fppf families preserving the original Cartier subgroup. -/
theorem exists_hom_divisor_fppf_cover [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (cyclicHomAuxiliaryScheme n).left)
      (J : ∀ i, (cyclicHomSourceCurve n (p i)).FiniteSubgroup n),
      ∀ i, (J i).ideal = cyclicHomSourceIdeal n (p i) ∧
        (∃ P, (J i).IsCartierGenerator P) ∧
          Nonempty (CompatibleIso (J i) (H.baseChange (C.f i))) := by
  have h (x : S) := exists_original_hom_divisor_neighborhood H hc h₂
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hx hV p J hJ using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, p, J, hJ⟩

/-- Smooth-locus neighborhoods retain non-etale subgroups even in partly singular families. -/
theorem exists_smoothLocus_hom_divisor_neighborhood {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (p : U ⟶ (cyclicHomAuxiliaryScheme n).left)
          (J : (cyclicHomSourceCurve n p).FiniteSubgroup n),
          J.ideal = cyclicHomSourceIdeal n p ∧
            (∃ P, J.IsCartierGenerator P) ∧ Nonempty (CompatibleIso J (H.baseChange g)) := by
  let B := smoothBaseOpen E
  let _ : IsLocallyNoetherian B.toScheme := isLocallyNoetherian_of_isOpenImmersion B.ι
  let _ : Smooth (E.baseChange B.ι).curve.hom := SmoothOfRelativeDimension.smooth 1 _
  have hB₂ : IsUnit (2 : Γ(B.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h₂.map B.ι.appTop.hom
  obtain ⟨U, g, hg, hl, hxg, hV, p, J, hJ, hP, ⟨a⟩⟩ :=
    exists_original_hom_divisor_neighborhood (H.baseChange B.ι) (hc.baseChange H B.ι) hB₂
      (x := (⟨x, hx⟩ : B.toScheme)) (V := B.ι ⁻¹ᵁ V) hxV
  let _ := hg
  let _ := hl
  refine ⟨U, g ≫ B.ι, inferInstance, inferInstance, ?_, ?_, p, J, hJ, hP,
    ⟨a.trans (compatibleBaseChangeComp H B.ι g).symm⟩⟩
  · obtain ⟨u, hu⟩ := hxg
    exact ⟨u, by change B.ι (g u) = x; rw [hu]; rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨u, rfl⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
