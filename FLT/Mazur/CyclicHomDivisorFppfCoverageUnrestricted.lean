/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalHomDivisorCoverageUnrestricted
public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension
public import FLT.Mazur.CyclicHomUniversalSubgroupComparison

/-!
# Fppf families retaining non-etale orbit divisors

These results hold over arbitrary bases, without Noetherian assumptions.
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
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include hc h₂

/-- Smooth cyclic objects have small fppf families preserving the original Cartier subgroup. -/
theorem exists_hom_divisor_fppf_cover_unrestricted [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (cyclicHomAuxiliaryScheme n).left)
      (J : ∀ i, (cyclicHomSourceCurve n (p i)).FiniteSubgroup n),
      ∀ i, (J i).ideal = cyclicHomSourceIdeal n (p i) ∧
        (∃ P, (J i).IsCartierGenerator P) ∧
          Nonempty (CompatibleIso (J i) (H.baseChange (C.f i))) := by
  have h (x : S) := exists_original_hom_divisor_neighborhood_unrestricted H hc h₂
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hx hV p J hJ using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, p, J, hJ⟩

/-- Smooth-locus neighborhoods retain non-etale subgroups even in partly singular families. -/
theorem exists_smoothLocus_hom_divisor_neighborhood_unrestricted {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (p : U ⟶ (cyclicHomAuxiliaryScheme n).left)
          (J : (cyclicHomSourceCurve n p).FiniteSubgroup n),
          J.ideal = cyclicHomSourceIdeal n p ∧
            (∃ P, J.IsCartierGenerator P) ∧ Nonempty (CompatibleIso J (H.baseChange g)) := by
  let B := smoothBaseOpen E
  let _ : Smooth (E.baseChange B.ι).curve.hom := SmoothOfRelativeDimension.smooth 1 _
  have hB₂ : IsUnit (2 : Γ(B.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h₂.map B.ι.appTop.hom
  obtain ⟨U, g, hg, hl, hxg, hV, p, J, hJ, hP, ⟨a⟩⟩ :=
    exists_original_hom_divisor_neighborhood_unrestricted (H.baseChange B.ι) (hc.baseChange H B.ι)
      hB₂
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

/-!
# Unrestricted original cyclic subgroup covers factor through the global closed locus

The existing fppf cover retains the full original subgroup and its Cartier
generator. Each unchanged auxiliary parameter factors through the actual
global multiplication locus. No Noetherian base hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include hc h₂ in
/-- The original finite subgroup cover has actual points of the global closed cyclic locus. -/
theorem exists_hom_locus_fppf_cover_unrestricted [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (cyclicHomAuxiliaryScheme n).left)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n)
      (J : ∀ i, (cyclicHomSourceCurve n (p i)).FiniteSubgroup n),
      ∀ i, q i ≫ cyclicHomUniversalMultiplicationLocusInclusion n = p i ∧
        (J i).ideal = cyclicHomSourceIdeal n (p i) ∧
          (∃ P, (J i).IsCartierGenerator P) ∧
            Nonempty (CompatibleIso (J i) (H.baseChange (C.f i))) := by
  obtain ⟨C, p, J, hJ⟩ := H.exists_hom_divisor_fppf_cover_unrestricted hc h₂
  have hz i := cyclicHomMultiplicationEquation_of_subgroup n (p i) (J i) (hJ i).1
  exact ⟨C, p, (fun i ↦ cyclicHomUniversalLocusLift n (p i) (hz i)), J,
    fun i ↦ ⟨cyclicHomUniversalLocusLift_inclusion n (p i) (hz i), hJ i⟩⟩

include hc h₂ in
/-- The actual universal subgroup covers every original smooth cyclic subgroup fppf locally. -/
theorem exists_universal_hom_subgroup_fppf_cover_unrestricted [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n),
      ∀ i, Nonempty (CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange (q i))
        (H.baseChange (C.f i))) := by
  obtain ⟨C, p, q, J, hJ⟩ := H.exists_hom_locus_fppf_cover_unrestricted hc h₂
  refine ⟨C, q, fun i ↦ ?_⟩
  obtain ⟨a⟩ := (hJ i).2.2.2
  exact ⟨(cyclicHomUniversalSubgroupIsoOfFactorization n (q i) (p i)
    (hJ i).1 (J i) (hJ i).2.1).trans a⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
