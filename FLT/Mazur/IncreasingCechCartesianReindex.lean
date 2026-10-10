/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCartesianDifferential

/-!
# Reindexing actual cartesian chart sections

Finite intersections commute with inverse image. Restriction along this equality
identifies the cartesian chart complex with the bounded complex on the actual
inverse-image cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero

variable {P X T : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ T)
  {ι : Type} [LinearOrder ι] (U : ι → X.Opens)

/-- The actual tuple intersection commutes with inverse image. -/
lemma preimage_tuple (n : ℕ) (a : Tuple (ι := ι) n) :
    p ⁻¹ᵁ V U n a.val = V (fun i ↦ p ⁻¹ᵁ U i) n a.val := by
  apply TopologicalSpace.Opens.ext
  simp only [V, Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_iInf,
    Set.preimage_iInter]

/-- Equal opens have a canonical base-linear section equivalence. -/
def equalOpenSections {Y : Scheme.{0}} (M : Y.Modules) {R : Type} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) {A B : Y.Opens} (h : A = B) :
    baseSections M ρ A ≃ₗ[R] baseSections M ρ B := by
  subst B
  exact LinearEquiv.refl R _

/-- The equal-open comparison is the actual restriction. -/
lemma equalOpenSections_apply {Y : Scheme.{0}} (M : Y.Modules) {R : Type} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) {A B : Y.Opens} (h : A = B) (x : baseSections M ρ A) :
    equalOpenSections M ρ h x = baseRestriction M ρ h.ge x := by
  subst B
  change x = M.presheaf.map (𝟙 _ ) x
  exact (ConcreteCategory.congr_hom (M.presheaf.map_id (Opposite.op A)) x).symm

/-- Cartesian chart coordinates give the actual bounded term of the inverse-image cover. -/
def chartTermEquiv (n : ℕ) :
    ChartTerm (p := p) (q := q) U n ≃ₗ[Γ(T, ⊤)]
      BaseTerm (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n :=
  (LinearEquiv.piCongrRight fun a ↦
    equalOpenSections (structureModule P) q.appTop.hom (preimage_tuple p U n a)).trans
      (baseTermCoordinates (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n).symm

/-- The reindexing map uses actual restrictions along equal tuple opens. -/
lemma chartTermEquiv_apply (n : ℕ) (x : ChartTerm (p := p) (q := q) U n)
    (a : Tuple (ι := ι) n) :
    baseTermCoordinates (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n
      (chartTermEquiv p q U n x) a =
        baseRestriction (structureModule P) q.appTop.hom (preimage_tuple p U n a).ge (x a) :=
  equalOpenSections_apply _ _ _ _

/-- Reindexing preserves the signed actual restriction differential. -/
lemma chartTermEquiv_d (n : ℕ) (x : ChartTerm (p := p) (q := q) U n) :
    chartTermEquiv p q U (n + 1) (chartD U n x) =
      baseD (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n
        (chartTermEquiv p q U n x) := by
  apply (baseTermCoordinates (structureModule P) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom (n + 1)).injective
  funext a
  rw [chartTermEquiv_apply, chartD_apply, map_sum, baseD_coordinates]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, chartTermEquiv_apply]
  congr 1
  change ((baseRestriction (structureModule P) q.appTop.hom _).comp
    (baseRestriction (structureModule P) q.appTop.hom _)) _ =
      ((baseRestriction (structureModule P) q.appTop.hom _).comp
        (baseRestriction (structureModule P) q.appTop.hom _)) _
  rw [baseRestriction_comp, baseRestriction_comp]
  rfl

end FLT.Mazur.IncreasingCechCartesian
