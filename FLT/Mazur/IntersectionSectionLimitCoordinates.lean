/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompactOpenAmbientSectionDescent
public import FLT.Mazur.CocycleGlobalCoordinates
public import FLT.Mazur.IntersectionCocyclePullbackRecovery

/-!
# Descending genuine global-section coordinates

For a fixed cocycle at a finite stage, finitely many global sections of its
inverse-image cocycle have coordinates at one later stage. The coordinates
retain restriction, transition and recovery identities on every intersection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

/-- A chart in an intersection, together with a section label. -/
abbrev IntersectionSectionLabel {ι : Type u} (T : Type u) (s : NonemptyChartSet ι) :=
  {i // i ∈ s.val} × T

/-- Restricting an intersection retains its chart and section labels. -/
def intersectionSectionLabelMap {ι T : Type u} {s t : NonemptyChartSet ι} (f : s ⟶ t)
    (k : IntersectionSectionLabel T s) : IntersectionSectionLabel T t :=
  (⟨k.1.val, leOfHom f k.1.property⟩, k.2)

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- The coordinates of actual global sections descend with their transition equations. -/
theorem exists_intersectionSection_limit_coordinates {ι T : Type u} [Finite ι] [Finite T]
    (i : I) (U : ι → (D.obj i).Opens)
    (hcompact : ∀ s, IsCompact (finiteIntersectionOpen U s : Set (D.obj i)))
    (g : Cocycle U) (σ : T → (g.inverseImage (c.π.app i)).sections ⊤) :
    ∃ (r : Over i)
      (y : ∀ s, IntersectionSectionLabel T s →
        Γ(D.obj r.left, D.map r.hom ⁻¹ᵁ finiteIntersectionOpen U s)),
      (∀ s k, (c.π.app r.left).appLE _ _
        (by rw [← Scheme.Hom.comp_preimage, c.w]) (y s k) =
          (g.inverseImage (c.π.app i)).globalCoordinate (σ k.2) k.1.val _
            ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1))) ∧
      (∀ {s t} (h : s ≤ t) k, res ((D.map r.hom).preimage_mono
          (finiteIntersectionOpen_antitone U h)) (y s k) =
            y t (intersectionSectionLabelMap (homOfLE h) k)) ∧
      ∀ s (k : IntersectionPair s) l,
        y s (k.1, l) = (D.map r.hom).app (finiteIntersectionOpen U s)
          (g.unit k.1.val k.2.val _ (finiteIntersectionOpen_le_chart U s k.1)
            (finiteIntersectionOpen_le_chart U s k.2) : Γ(D.obj i, _)) * y s (k.2, l) := by
  let O := finiteIntersectionOpen U
  let G := g.inverseImage (c.π.app i)
  let x (s : NonemptyChartSet ι) (k : IntersectionSectionLabel T s) :=
    G.globalCoordinate (σ k.2) k.1.val (c.π.app i ⁻¹ᵁ O s)
      ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1))
  let v (s : NonemptyChartSet ι) (k : IntersectionPair s × T) : Γ(D.obj i, O s) :=
    g.unit k.1.1.val k.1.2.val _ (finiteIntersectionOpen_le_chart U s k.1.1)
      (finiteIntersectionOpen_le_chart U s k.1.2)
  have hx {s t : NonemptyChartSet ι} (f : s ⟶ t) (k : IntersectionSectionLabel T s) :
      res ((c.π.app i).preimage_mono (finiteIntersectionOpen_antitone U (leOfHom f)))
        (x s k) = x t (intersectionSectionLabelMap f k) :=
    G.globalCoordinate_restrict _ _ _ _
  have hv (s : NonemptyChartSet ι) (k : IntersectionPair s × T) :
      x s (k.1.1, k.2) = (c.π.app i).app (O s) (v s k) * x s (k.1.2, k.2) := by
    dsimp only [x]
    rw [G.globalCoordinate_transition (σ k.2) k.1.1.val k.1.2.val _
      ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1.1))
      ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1.2))]
    congr 1
    simpa only [G, Cocycle.inverseImage, v, Scheme.Hom.app_eq_appLE] using
      g.inverseImageUnit_eq (c.π.app i) k.1.1.val k.1.2.val _
        ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1.1))
        ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k.1.2)) (O s)
        (finiteIntersectionOpen_le_chart U s k.1.1)
        (finiteIntersectionOpen_le_chart U s k.1.2) le_rfl
  obtain ⟨r, y, hy, hnat, hv'⟩ := exists_compactOpen_ambient_sections D c hc i O
    (fun f ↦ finiteIntersectionOpen_antitone U (leOfHom f)) hcompact
    (IntersectionSectionLabel T) (fun s ↦ IntersectionPair s × T) x
    (fun f ↦ intersectionSectionLabelMap f) hx
    (fun _ k ↦ (k.1.1, k.2)) (fun _ k ↦ (k.1.2, k.2)) v hv
  exact ⟨r, y, hy, fun h k ↦ hnat (homOfLE h) k, fun s k l ↦ hv' s (k, l)⟩

end FLT.Mazur.Approximation
