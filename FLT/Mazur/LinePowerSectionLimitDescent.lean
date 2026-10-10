/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CocycleGlobalSectionLimitDescent
public import FLT.Mazur.CocycleSectionOpenComparison
public import FLT.Mazur.LinePowerCocyclePullback

/-!
# Descending specified power sections and recovering their opens

Transport actual sections into the inverse-image cocycle of a finite-stage
power, descend their coordinates, and recover actual power sections at a
refinement. Cone composition identifies their generator opens exactly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (Cone IsLimit)
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Specified power sections descend with exact recovery of all generator opens. -/
theorem exists_linePowerSections_of_limit {ι T : Type u} [Finite ι] [Finite T]
    (i : I) (L : (D.obj i).Modules) (n : ℕ) (U : ι → (D.obj i).Opens)
    (hU : iSup U = ⊤)
    (hcompact : ∀ s, IsCompact (finiteIntersectionOpen U s : Set (D.obj i)))
    (e : ∀ k, (tensorPower L n).restrict (U k).ι ≅ structureModule (U k).toScheme)
    (s : T → Γ(tensorPower ((pullback (c.π.app i)).obj L) n, ⊤)) :
    ∃ (r : Over i) (t : T → Γ(tensorPower ((pullback (D.map r.hom)).obj L) n, ⊤)),
      ∀ l, c.π.app r.left ⁻¹ᵁ
          sectionGeneratorOpen (tensorPower ((pullback (D.map r.hom)).obj L) n) (t l) =
        sectionGeneratorOpen (tensorPower ((pullback (c.π.app i)).obj L) n) (s l) := by
  let g := lineTrivializationCocycle e
  let σ (l : T) := linePowerCocycleSection L n e hU (c.π.app i) (s l)
  obtain ⟨r, τ, hτ⟩ := exists_cocycleGlobalSections_of_limit D c hc i U hcompact g σ
  let E := linePowerCocyclePullbackIso L n e hU (D.map r.hom)
  refine ⟨r, fun l ↦ E.hom.app ⊤ (τ l), fun l ↦ ?_⟩
  have hopen : sectionGeneratorOpen (g.inverseImage (c.π.app i)).sheaf (σ l) =
      c.π.app r.left ⁻¹ᵁ sectionGeneratorOpen (g.inverseImage (D.map r.hom)).sheaf (τ l) := by
    apply Cocycle.inverseImage_sectionGeneratorOpen_composition g hU (D.map r.hom)
      (c.π.app r.left) (c.π.app i) (c.w r.hom) (τ l) (σ l)
    intro k
    have h := hτ l (singletonChartSet k) ⟨k, by simp [singletonChartSet]⟩
    let P (A : (D.obj i).Opens) (hk : A ≤ U k) : Prop :=
      (c.π.app r.left).appLE (D.map r.hom ⁻¹ᵁ A) (c.π.app i ⁻¹ᵁ A)
          (by rw [← Scheme.Hom.comp_preimage, c.w])
          ((g.inverseImage (D.map r.hom)).globalCoordinate (τ l) k _
            ((D.map r.hom).preimage_mono hk)) =
        (g.inverseImage (c.π.app i)).globalCoordinate (σ l) k _
          ((c.π.app i).preimage_mono hk)
    have hP : ∀ hk, P (finiteIntersectionOpen U (singletonChartSet k)) hk := fun _ ↦ h
    have hQ : ∀ hk, P (U k) hk :=
      Eq.mp (congrArg (fun A ↦ ∀ hk, P A hk) (finiteIntersectionOpen_singleton U k)) hP
    exact hQ le_rfl
  rw [sectionGeneratorOpen_iso E]
  exact hopen.symm.trans (linePowerCocycleSection_generatorOpen L n e hU (c.π.app i) (s l))

end FLT.Mazur.Approximation
