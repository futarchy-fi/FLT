/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalLocalCubicUnrestricted
public import FLT.Mazur.PointedCubicIndependentSourceSubgroup
public import FLT.Mazur.EtaleCyclicOriginalNormalizedCoverageUnrestricted
public import FLT.Mazur.IndependentCyclicModuliPullback
public import FLT.Mazur.EtaleCyclicNormalizedImageSieveUnrestricted

/-!
# Unrestricted original smooth cyclic coverage without coprimality with four

The independent chart retains the original full curve and Cartier subgroup.
Its auxiliary and cyclic labels may intersect, so the construction now covers
even cyclic orders too. Two must still be invertible and the subgroup etale.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- Independent charts cover every original smooth etale object, including even orders. -/
theorem exists_original_independent_neighborhood_unrestricted {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ (independentCyclicAuxiliaryScheme n).left,
          independentCyclicSourceModuliClass n p =
            ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, φ, hφ, ⟨a⟩⟩ :=
    hc.exists_original_local_cubic_unrestricted H hx
  let _ := hT
  let _ := hW
  let _ := hf
  let _ := hl
  have hT₂ : IsUnit (2 : Γ(T, ⊤)) := by
    simpa only [map_ofNat] using h₂.map f.appTop.hom
  let k := (pointedCubicAuxiliaryCover W hT₂).hom
  let _ : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₂
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₂
  refine ⟨(pointedCubicAuxiliaryCover W hT₂).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_,
    (pointedCubicIndependentParameter W hT₂ φ hφ).left, ?_⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩
  · rw [pointedCubicIndependentSource_originalClass W hT₂ φ hφ (H.baseChange f) a
      (hc.baseChange H f) (ha.baseChange f)]
    exact (congrFun (ampleCyclicClassesPullback_comp f k n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-!
# Unrestricted original smooth-locus coverage without coprimality with four

A generalized curve may have singular fibers elsewhere. Restrict its actual
subgroup to the canonical smooth base open, apply the proved smooth coverage,
and flatten the resulting map and modular pullback to the original base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- Every original smooth-locus point is covered by an actual independent cyclic chart. -/
theorem exists_smoothLocus_independent_neighborhood_unrestricted {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ (independentCyclicAuxiliaryScheme n).left,
          independentCyclicSourceModuliClass n p =
            ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  let B := smoothBaseOpen E
  let _ : Smooth (E.baseChange B.ι).curve.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  let _ : Etale (H.baseChange B.ι).carrier.hom :=
    inferInstanceAs (Etale (pullback.snd H.carrier.hom B.ι))
  have hB₂ : IsUnit (2 : Γ(B.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h₂.map B.ι.appTop.hom
  obtain ⟨U, g, hg, hl, hxg, hV, p, hp⟩ :=
    exists_original_independent_neighborhood_unrestricted (H.baseChange B.ι)
      (hc.baseChange H B.ι) (ha.baseChange B.ι) hB₂
      (x := (⟨x, hx⟩ : B.toScheme)) (V := B.ι ⁻¹ᵁ V) hxV
  let _ := hg
  let _ := hl
  refine ⟨U, g ≫ B.ι, inferInstance, inferInstance, ?_, ?_, p, ?_⟩
  · obtain ⟨u, hu⟩ := hxg
    exact ⟨u, by change B.ι (g u) = x; rw [hu]; rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨u, rfl⟩
  · exact hp.trans ((congrFun (ampleCyclicClassesPullback_comp B.ι g n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)).symm)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-!
# Unrestricted fppf coverage by independent cyclic charts at all positive orders

The constructed original parameters form an actual fppf family. Their image
sieve covers the original modular class and stays covering on every test scheme.
No coprimality between the cyclic order and four is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂

/-- Every original smooth etale cyclic object has an actual independent fppf presentation. -/
theorem exists_independent_fppf_cover_unrestricted :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (independentCyclicAuxiliaryScheme n).left),
      ∀ i, independentCyclicSourceModuliClass n (p i) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  have h (x : S) := exists_original_independent_neighborhood_unrestricted H hc ha h₂
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hx hV p hp using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, p, hp⟩

/-- The independent chart's actual image covers every original class in this sector. -/
theorem independent_imageSieve_mem_unrestricted :
    Presheaf.imageSieve (independentCyclicModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := exists_independent_fppf_cover_unrestricted H hc ha h₂
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

/-- Independent chart coverage persists on arbitrary, possibly nonnoetherian, tests. -/
theorem independent_pullback_imageSieve_mem_unrestricted {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (independentCyclicModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g (independent_imageSieve_mem_unrestricted H hc ha
    h₂)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
