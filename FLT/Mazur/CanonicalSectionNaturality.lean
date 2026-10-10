/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CanonicalLineSectionBaseChange

/-!
# Naturality of the canonical section comparison

Actual morphisms of module sheaves commute with arbitrary affine section
base change. The statement applies to the constructed line equivalences and
does not require compatible choices of affine covers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open FCurve Chow

variable {X : Scheme.{0}} {R : Type} [CommRing R]

/-- The actual map on global sections, linear over a specified structural base. -/
def baseGlobalSectionMap (ρ : R →+* Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    baseSections M ρ ⊤ →ₗ[R] baseSections N ρ ⊤ where
  toFun := φ.app ⊤
  map_add' := map_add (φ.app ⊤).hom
  map_smul' r s := φ.app_smul (X.presheaf.map (𝟙 _) (ρ r)) s

variable {P T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) {M N : X.Modules} (φ : M ⟶ N)

/-- Canonical section base change is natural in every morphism of coefficient sheaves. -/
lemma globalComparison_naturality :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    (baseGlobalSectionMap q.appTop.hom ((pullback p).map φ)).comp (globalComparison h M) =
      (globalComparison h N).comp
        (AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤) (baseGlobalSectionMap f.appTop.hom φ)) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b s =>
    change baseGlobalSectionMap q.appTop.hom ((pullback p).map φ)
      (globalComparison h M (b ⊗ₜ[Γ(S, ⊤)] s)) =
        globalComparison h N (b ⊗ₜ[Γ(S, ⊤)] baseGlobalSectionMap f.appTop.hom φ s)
    rw [globalComparison_tmul, map_smul, globalComparison_tmul]
    congr 1
    exact pullGlobal_naturality p φ s

end FLT.Mazur.IncreasingCechCoefficients

namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S]
  [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat f]
  (h : IsPullback p q f g) {L K : X.Modules} (φ : L ⟶ K)
  (hL : LocallyFreeRankOne L) (hK : LocallyFreeRankOne K)
  (hHL : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)))
  (hHK : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom K (n + 1)))

/-- The constructed line-section equivalences form a natural comparison in the line sheaf. -/
lemma sectionsEquiv_naturality :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    (baseGlobalSectionMap q.appTop.hom ((pullback p).map φ)).comp
        (sectionsEquiv f L hL hHL h).toLinearMap =
      (sectionsEquiv f K hK hHK h).toLinearMap.comp
        (AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤) (baseGlobalSectionMap f.appTop.hom φ)) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  rw [sectionsEquiv_eq, sectionsEquiv_eq]
  exact globalComparison_naturality h φ

end FLT.Mazur.LineSectionBaseChange
