/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitelyPresentedImmersedProperCover
public import FLT.Mazur.ProperCoverLimitDescent

/-!
# Eventual properness of closed finite-presentation approximations

Constructing a proper immersed cover at a finitely presented stage makes
properness descend from the closed inverse limit. Only the finite stage,
not the original limit morphism, is assumed finitely presented.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]

include hc in
/-- A finitely presented separated ambient stage has a proper closed refinement. -/
theorem exists_isProper_of_closed_system {R : Type u} [CommRing R] {X : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj X) [∀ i, IsClosedImmersion (t.app i)]
    (b : c.pt ⟶ X) [IsClosedImmersion b] (hb : ∀ i, c.π.app i ≫ t.app i = b)
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] [IsProper (b ≫ f)] :
    ∃ i, IsProper (t.app i ≫ f) := by
  obtain ⟨Z, P, π, p, h, hπ, hs, hp, hh, hqc, w⟩ :=
    exists_finitelyPresented_immersed_proper_cover f
  let _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let _ : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated π
  let _ : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  exact exists_isProper_of_immersed_cover D c hc t b hb f p π h w

include hc in
/-- Properness of a closed inverse limit occurs above any suitable finite stage. -/
theorem exists_isProper_of_closed_limit (i : I) {R : Type u} [CommRing R]
    (f : D.obj i ⟶ Spec (.of R)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] [IsClosedImmersion (c.π.app i)]
    [IsProper (c.π.app i ≫ f)] :
    ∃ (j : I) (g : j ⟶ i), IsProper (D.map g ≫ f) := by
  let F := Over.forget i ⋙ D
  let d := c.whisker (Over.forget i)
  let t : F ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality j k g := by
        change D.map g.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, Over.w g, Category.comp_id] }
  let _ (j : Over i) : IsClosedImmersion (t.app j) := inferInstanceAs
    (IsClosedImmersion (D.map j.hom))
  let _ {j k : Over i} (g : j ⟶ k) : IsClosedImmersion (F.map g) :=
    inferInstanceAs (IsClosedImmersion (D.map g.left))
  obtain ⟨j, hj⟩ := exists_isProper_of_closed_system F d
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc) t (c.π.app i)
    (fun j ↦ c.w j.hom) f
  exact ⟨j.left, j.hom, hj⟩

end FLT.Mazur.Approximation
