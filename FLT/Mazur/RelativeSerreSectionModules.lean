/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineSectionProjective
public import FLT.Mazur.ClosedProjectiveSerreVanishing
public import FLT.Mazur.LinePowerSectionBaseChange
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# Eventual finite projective sections and arbitrary affine base change

For a flat closed projective family over a Noetherian ring, a single Serre
bound makes every later hyperplane-line power have finite projective sections.
Those sections commute with every affine change of base, including nonflat and
non-Noetherian bases. Both coefficients are actual tensor powers of the line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
open FCurve Chow LineSectionBaseChange ModuleLineBundleTensorPullback

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} {d : ℕ}
  (i : X ⟶ space R (Fin (d + 1))) [IsClosedImmersion i]
  [Flat (i ≫ baseProjection R _)] (L : X.Modules)
  (e : L ≅ (pullback i).obj (twistingSheaf R (Fin (d + 1)) 1))

include e in
/-- One bound gives finite projective sections and universal affine base change in every degree. -/
theorem exists_eventual_projective_sections_baseChange :
    ∃ N : ℕ, ∀ n ≥ N,
      Module.Finite Γ(Spec (.of R), ⊤)
        (baseSections (tensorPower L n) (i ≫ baseProjection R _).appTop.hom ⊤) ∧
      Module.Projective Γ(Spec (.of R), ⊤)
        (baseSections (tensorPower L n) (i ≫ baseProjection R _).appTop.hom ⊤) ∧
      ∀ {P T : Scheme.{0}} [IsAffine T] {p : P ⟶ X} {q : P ⟶ T}
        {g : T ⟶ Spec (.of R)}, IsPullback p q (i ≫ baseProjection R _) g →
        let _ : Algebra Γ(Spec (.of R), ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
        Nonempty (Γ(T, ⊤) ⊗[Γ(Spec (.of R), ⊤)]
          baseSections (tensorPower L n) (i ≫ baseProjection R _).appTop.hom ⊤ ≃ₗ[Γ(T, ⊤)]
            baseSections (tensorPower ((pullback p).obj L) n) q.appTop.hom ⊤) := by
  let f := i ≫ baseProjection R (Fin (d + 1))
  let _ : IsProper f := inferInstance
  let _ : IsNoetherianRing Γ(Spec (.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let _ := Chow.source_isNoetherian f
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  have hL : LocallyFreeRankOne L :=
    ((twistingSheaf_locallyFreeRankOne R (Fin (d + 1)) 1).pullback i).of_iso e.symm
  obtain ⟨N, hN⟩ := exists_line_power_moduleH_subsingleton_of_projective_embedding
    R (Fin (d + 1)) i L e
  refine ⟨N, fun n hn ↦ ?_⟩
  let _ := (hL.tensorPower n).isFinitePresentation
  refine ⟨proper_sections_finite f (tensorPower L n),
    proper_acyclic_sections_projective f (tensorPower L n) (hL.tensorPower n) (hN n hn), ?_⟩
  intro P T _ p q g h
  let _ : Algebra Γ(Spec (.of R), ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact ⟨(acyclicSectionsEquiv f (tensorPower L n) (hL.tensorPower n) (hN n hn) h).trans
    (LinePowerSectionBaseChange.powerSectionsIso (p := p) (q := q) L n).toLinearEquiv⟩

end FLT.Mazur.ProjectiveSpace
