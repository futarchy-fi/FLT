/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicFiniteEtale
public import FLT.Mazur.ConstantCyclicSectionMap
public import FLT.Mazur.DisjointClosedCoproduct
public import FLT.Mazur.RationalFibers
public import FLT.Mazur.SectionDivisors

/-!
# Closed cyclic subgroup maps from distinct rational sections

Distinct rational sections have disjoint images over a field. The finite
disjoint union theorem therefore makes an injective cyclic family a closed
immersion, with its actual ideal equal to the product of the section ideals.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.ConstantCyclicSectionClosed

variable {K : Type} [Field K] {n : ℕ} [NeZero n]
  {G : Over (Spec (.of K))} [GrpObj G]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over (Spec (.of K))) ⟶ G))

open ConstantCyclicSectionMap ConstantCyclicFiniteEtale

/-- An injective family of rational sections has pairwise disjoint images. -/
theorem sections_disjoint {Index : Type*} {X : Over (Spec (.of K))}
    (s : Index → Sections X) (hs : Function.Injective s) :
    Pairwise fun i j ↦ Disjoint (Set.range (s i).left) (Set.range (s j).left) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  apply hij
  exact hs (Sections.point_injective (by
    exact (Sections.apply_eq_point (s i) x).symm.trans
      (hy.symm.trans (Sections.apply_eq_point (s j) y))))

omit [NeZero n] in
/-- Distinct rational sections in the cyclic family have disjoint images. -/
theorem disjoint (hφ : Function.Injective φ) :
    Pairwise fun i j : ZMod n ↦
      Disjoint (Set.range (φ (Multiplicative.ofAdd i)).left)
        (Set.range (φ (Multiplicative.ofAdd j)).left) :=
  sections_disjoint _ fun _ _ h ↦ congrArg Multiplicative.toAdd (hφ h)

/-- The underlying scheme map is the coproduct of the original sections. -/
@[reassoc]
theorem underlying_toScheme :
    (underlyingIso K n).hom ≫ (toScheme φ).left =
      Sigma.desc (fun i : ZMod n ↦ (φ (Multiplicative.ofAdd i)).left) := by
  apply Sigma.hom_ext
  intro i
  rw [component_underlyingIso_assoc, Sigma.ι_comp_desc]
  exact congrArg Over.Hom.left (component_toScheme φ i)

/-- Injectivity on rational sections gives a genuine closed immersion of group schemes. -/
theorem closed [IsSeparated G.hom] (hφ : Function.Injective φ) :
    IsClosedImmersion (toScheme φ).left := by
  have (i : ZMod n) : IsClosedImmersion (φ (Multiplicative.ofAdd i)).left :=
    FCurve.isClosedImmersion_section G.hom _ (φ (Multiplicative.ofAdd i)).w
  have hc := DisjointClosedCoproduct.closed
    (fun i : ZMod n ↦ (φ (Multiplicative.ofAdd i)).left) (disjoint φ hφ)
  rw [← underlying_toScheme φ] at hc
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsClosedImmersion)
    (underlyingIso K n).hom (toScheme φ).left).mp hc

/-- The subgroup kernel retains every section with multiplicity one. -/
theorem product_eq_kernel [IsSeparated G.hom] (hφ : Function.Injective φ) :
    (∏ i : ZMod n, (φ (Multiplicative.ofAdd i)).left.ker) = (toScheme φ).left.ker := by
  have (i : ZMod n) : IsClosedImmersion (φ (Multiplicative.ofAdd i)).left :=
    FCurve.isClosedImmersion_section G.hom _ (φ (Multiplicative.ofAdd i)).w
  rw [DisjointClosedCoproduct.product_eq_kernel _ (disjoint φ hφ),
    ← underlying_toScheme φ, Scheme.Hom.ker_comp_of_isIso]

/-- Any map out of the constant scheme is the coproduct of its component sections. -/
@[reassoc]
theorem underlying_components {X : Over (Spec (.of K))}
    (d : ConstantCyclicGroup.model (Spec (.of K)) n ⟶ X) :
    (underlyingIso K n).hom ≫ d.left = Sigma.desc (fun i : ZMod n ↦
      (ConstantCyclicGroup.component (Spec (.of K)) n i ≫ d).left) := by
  apply Sigma.hom_ext
  intro i
  rw [component_underlyingIso_assoc, Sigma.ι_comp_desc]
  rfl

/-- A map with distinct components has the product of their ideals as its actual kernel. -/
theorem kernel_eq_component_product {X : Over (Spec (.of K))} [IsSeparated X.hom]
    (d : ConstantCyclicGroup.model (Spec (.of K)) n ⟶ X)
    (hd : Function.Injective (fun i : ZMod n ↦
      ConstantCyclicGroup.component (Spec (.of K)) n i ≫ d)) :
    d.left.ker = ∏ i : ZMod n,
      (ConstantCyclicGroup.component (Spec (.of K)) n i ≫ d).left.ker := by
  let s := fun i : ZMod n ↦ ConstantCyclicGroup.component (Spec (.of K)) n i ≫ d
  have (i : ZMod n) : IsClosedImmersion (s i).left :=
    FCurve.isClosedImmersion_section X.hom _ (s i).w
  rw [← Scheme.Hom.ker_comp_of_isIso (underlyingIso K n).hom d.left,
    underlying_components]
  exact (DisjointClosedCoproduct.product_eq_kernel
    (fun i : ZMod n ↦ (s i).left) (sections_disjoint s hd)).symm

end FLT.Mazur.ConstantCyclicSectionClosed
