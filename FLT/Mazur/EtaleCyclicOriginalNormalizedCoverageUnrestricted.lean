/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalLocalCubicUnrestricted
public import FLT.Mazur.PointedCubicNormalizedOriginalClass
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# Unrestricted full normalized charts cover original smooth etale cyclic objects locally

Over an arbitrary base with two invertible and cyclic order coprime to
four, each original smooth ample etale cyclic object is represented by the full
normalized slice on flat finitely presented neighborhoods covering every base
point. The represented modular class is the actual original pullback class.
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
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- The full normalized slice covers each original smooth etale cyclic object locally. -/
theorem exists_original_normalized_neighborhood_unrestricted {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ cyclicNormalizedSlice n,
          (cyclicNormalizedSliceModuliMap n).app (Opposite.op U) (ULift.up p) =
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
  have hk : AlgebraicGeometry.Surjective k := pointedCubicAuxiliaryCover_surjective W hT₂
  let _ := hk
  let _ : Etale k := pointedCubicAuxiliaryCover_etale W hT₂
  refine ⟨(pointedCubicAuxiliaryCover W hT₂).left, k ≫ f,
    inferInstance, inferInstance, ?_, ?_, pointedCubicNormalizedPoint W hT₂ φ hφ hn, ?_⟩
  · obtain ⟨t, ht⟩ := hxf
    obtain ⟨u, hu⟩ := k.surjective t
    exact ⟨u, by change f (k u) = x; rw [hu, ht]⟩
  · rintro _ ⟨u, rfl⟩
    exact hV ⟨k u, rfl⟩
  · rw [pointedCubicNormalizedPoint_originalClass W hT₂ φ hφ hn (H.baseChange f) a
      (hc.baseChange H f) (ha.baseChange f)]
    exact (congrFun (ampleCyclicClassesPullback_comp f k n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-!
# Unrestricted an actual fppf atlas for original smooth etale cyclic objects

Choose one proved normalized neighborhood at each base point. These form a
small fppf covering family, and every parameter represents the original class.
No finite subcover or global affineness hypothesis is needed.
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
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- The original object admits a small fppf family of actual full normalized parameters. -/
theorem exists_normalized_fppf_cover_unrestricted :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ cyclicNormalizedSlice n),
      ∀ i, (cyclicNormalizedSliceModuliMap n).app (Opposite.op (C.X i)) (ULift.up (p i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  have h (x : S) := exists_original_normalized_neighborhood_unrestricted H hc ha h₂ hn
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hx hV p hp using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, p, hp⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-!
# Unrestricted original smooth-locus coverage by the full normalized slice

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
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- Every original smooth-locus point is covered by an actual full normalized chart. -/
theorem exists_smoothLocus_normalized_neighborhood_unrestricted {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ p : U ⟶ cyclicNormalizedSlice n,
          (cyclicNormalizedSliceModuliMap n).app (Opposite.op U) (ULift.up p) =
            ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  let B := smoothBaseOpen E
  let _ : Smooth (E.baseChange B.ι).curve.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  let _ : Etale (H.baseChange B.ι).carrier.hom :=
    inferInstanceAs (Etale (pullback.snd H.carrier.hom B.ι))
  have hB₂ : IsUnit (2 : Γ(B.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h₂.map B.ι.appTop.hom
  obtain ⟨U, g, hg, hl, hxg, hV, p, hp⟩ :=
    exists_original_normalized_neighborhood_unrestricted (H.baseChange B.ι)
      (hc.baseChange H B.ι) (ha.baseChange B.ι) hB₂ hn
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
