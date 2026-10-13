/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalLocalCartierCubicUnrestricted
public import FLT.Mazur.OddWeierstrassPointedCubicHomRetainedSubgroup
public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension
public import FLT.Mazur.OddWeierstrassCyclicHomUniversalSubgroupComparison

/-!
# Unrestricted odd-chart original cyclic objects covered by multiplicity-preserving parameters

Every smooth original cyclic object has fppf local unrestricted parameters
whose orbit divisor is its actual subgroup under a full compatible comparison.
This includes non-etale levels. The ambient parameter scheme is not yet a
moduli chart: the subgroup condition still needs scheme-theoretic representation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hc h₃ in
/-- Non-etale cyclic levels have local parameters retaining the entire original subgroup ideal. -/
theorem exists_original_hom_divisor_neighborhood_unrestricted {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (p : U ⟶ (cyclicHomAuxiliaryScheme n).left)
          (J : (cyclicHomSourceCurve n p).FiniteSubgroup n),
          J.ideal = cyclicHomSourceIdeal n p ∧
            (∃ P, J.IsCartierGenerator P) ∧ Nonempty (CompatibleIso J (H.baseChange g)) := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, J, P, hP, ⟨a⟩⟩ :=
    hc.exists_original_local_cartierCubic_unrestricted H hx
  let _ := hT
  let _ := hW
  let _ := hf
  let _ := hl
  have hT₃ : IsUnit (3 : Γ(T, ⊤)) := by
    simpa only [map_ofNat] using h₃.map f.appTop.hom
  let φ := J.generatorCurveMarking hP
  let k := (pointedCubicAuxiliaryCover W hT₃).hom
  let _ : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₃
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₃
  refine ⟨(pointedCubicAuxiliaryCover W hT₃).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_,
    (pointedCubicHomAuxiliaryParameter W hT₃ φ).left,
    pointedCubicHomRetainedSubgroup W hT₃ φ J,
    pointedCubicHomRetained_ideal W hT₃ φ J hP rfl,
    ⟨J.pullGenerator k P, pointedCubicHomRetained_generator W hT₃ φ J hP⟩,
    ⟨(pointedCubicHomRetainedIso W hT₃ φ J).symm.trans
      ((a.baseChange k).trans (compatibleBaseChangeComp H f k).symm)⟩⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩

end FLT.Mazur.OddWeierstrassParameter

/-!
# Unrestricted odd-chart fppf families retaining non-etale orbit divisors

The local original comparisons give an actual small fppf cover for smooth
families, and neighborhoods on the smooth base locus of general families.
No modular map from the whole ambient parameter scheme is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hc h₃

/-- Smooth cyclic objects have small fppf families preserving the original Cartier subgroup. -/
theorem exists_hom_divisor_fppf_cover_unrestricted [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (cyclicHomAuxiliaryScheme n).left)
      (J : ∀ i, (cyclicHomSourceCurve n (p i)).FiniteSubgroup n),
      ∀ i, (J i).ideal = cyclicHomSourceIdeal n (p i) ∧
        (∃ P, (J i).IsCartierGenerator P) ∧
          Nonempty (CompatibleIso (J i) (H.baseChange (C.f i))) := by
  have h (x : S) := exists_original_hom_divisor_neighborhood_unrestricted H hc h₃
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
  have hB₃ : IsUnit (3 : Γ(B.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h₃.map B.ι.appTop.hom
  obtain ⟨U, g, hg, hl, hxg, hV, p, J, hJ, hP, ⟨a⟩⟩ :=
    exists_original_hom_divisor_neighborhood_unrestricted (H.baseChange B.ι) (hc.baseChange H B.ι)
      hB₃
      (x := (⟨x, hx⟩ : B.toScheme)) (V := B.ι ⁻¹ᵁ V) hxV
  let _ := hg
  let _ := hl
  refine ⟨U, g ≫ B.ι, inferInstance, inferInstance, ?_, ?_, p, J, hJ, hP,
    ⟨a.trans (compatibleBaseChangeComp H B.ι g).symm⟩⟩
  · obtain ⟨u, hu⟩ := hxg
    exact ⟨u, by change B.ι (g u) = x; rw [hu]; rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨u, rfl⟩

end FLT.Mazur.OddWeierstrassParameter

/-!
# Unrestricted odd-chart original cyclic subgroup covers factor through the global closed locus

The existing fppf cover retains the full original subgroup and its Cartier
generator. Each unchanged auxiliary parameter factors through the actual
global multiplication locus. No Noetherian base hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hc h₃ in
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
  obtain ⟨C, p, J, hJ⟩ := exists_hom_divisor_fppf_cover_unrestricted H hc h₃
  have hz i := cyclicHomMultiplicationEquation_of_subgroup n (p i) (J i) (hJ i).1
  exact ⟨C, p, (fun i ↦ cyclicHomUniversalLocusLift n (p i) (hz i)), J,
    fun i ↦ ⟨cyclicHomUniversalLocusLift_inclusion n (p i) (hz i), hJ i⟩⟩

include hc h₃ in
/-- The actual universal subgroup covers every original smooth cyclic subgroup fppf locally. -/
theorem exists_universal_hom_subgroup_fppf_cover_unrestricted [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n),
      ∀ i, Nonempty (CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange (q i))
        (H.baseChange (C.f i))) := by
  obtain ⟨C, p, q, J, hJ⟩ := exists_hom_locus_fppf_cover_unrestricted H hc h₃
  refine ⟨C, q, fun i ↦ ?_⟩
  obtain ⟨a⟩ := (hJ i).2.2.2
  exact ⟨(cyclicHomUniversalSubgroupIsoOfFactorization n (q i) (p i)
    (hJ i).1 (J i) (hJ i).2.1).trans a⟩

end FLT.Mazur.OddWeierstrassParameter
