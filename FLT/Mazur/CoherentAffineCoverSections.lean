/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentRestriction
public import FLT.Mazur.FiniteAffineCoverFiniteness

/-!
# Coherent sections on an affine cover

Local finite presentations restrict to the affine charts and their tuple
intersections. Sections are finite over each intersection's own ring of functions.
To apply the Noetherian base-ring finiteness theorem, the intersection sections
must additionally be finite over that base ring. Finiteness of the intersection
rings over the base is a sufficient extra hypothesis, proved below.

Neither coherence nor Noetherianity supplies that extra hypothesis: the structure
sheaf on the affine line over R has global sections R[t]. Thus these results give
a computation and a conditional finiteness reduction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero

variable {X : Scheme.{u}} (M : X.Modules) [M.IsFinitePresentation]

/-- Coherence transports to the actual open subscheme of any affine open. -/
theorem coherentAffineOpen_restrict (W : X.Opens) :
    (M.restrict W.ι).IsFinitePresentation :=
  coherent_restrict W.ι M

/-- An affine chart restriction is tilde of its own finite section module. -/
def coherentAffineOpenIso {W : X.Opens} (hW : IsAffineOpen W) :
    M.restrict hW.fromSpec ≅ tilde (moduleSpecΓFunctor.obj (M.restrict hW.fromSpec)) :=
  coherentAffineChartIso hW.fromSpec M

/-- The canonical spectrum chart has finite sections over the chart ring. -/
theorem coherentAffineOpen_chart_finite {W : X.Opens} (hW : IsAffineOpen W) :
    Module.Finite Γ(X, W) Γ(M.restrict hW.fromSpec, ⊤) :=
  coherent_affineChart_finite hW.fromSpec M

/-- Actual sections on an affine open are finite over its ring of functions. -/
theorem coherentAffineOpen_sections_finite {W : X.Opens} (hW : IsAffineOpen W) :
    Module.Finite Γ(X, W) (M.val.obj (op W)) := by
  let f := hW.fromSpec
  have _finiteChart := coherentAffineOpen_chart_finite M hW
  have _finiteGlobal := Module.Finite.of_restrictScalars_finite
    Γ(X, W) Γ(Spec Γ(X, W), ⊤) Γ(M.restrict f, ⊤)
  let g : Γ(M.restrict f, ⊤) →ₛₗ[(f.appIso ⊤).inv.hom] Γ(M, f ''ᵁ ⊤) :=
    { toFun := (M.restrictAppIso f ⊤).hom
      map_add' := map_add _
      map_smul' := fun r x ↦ M.smul_restrictAppIso_hom_apply f ⊤ r x }
  have hfinite := Module.Finite.of_surjective g
    ((ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective)
  have himage : f ''ᵁ ⊤ = W :=
    f.image_top_eq_opensRange.trans hW.opensRange_fromSpec
  rw [← himage]
  exact hfinite

variable {ι : Type u} [X.IsSeparated] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

omit [X.IsSeparated] in
/-- Each actual Cech intersection inherits a finite local presentation. -/
theorem coherentAffineCover_intersection_restrict (n : ℕ) (a : Fin (n + 1) → ι) :
    (M.restrict (Scheme.Opens.ι (V U n a))).IsFinitePresentation :=
  coherentAffineOpen_restrict M (V U n a)

include hU in
/-- Each Cech coordinate is finite over its own affine intersection ring. -/
theorem coherentAffineCover_intersection_finite (n : ℕ) (a : Fin (n + 1) → ι) :
    Module.Finite Γ(X, V U n a) (M.val.obj (op (V U n a))) :=
  coherentAffineOpen_sections_finite M (affineCover_intersection_isAffineOpen U hU n a)

variable {R : Type v} [Ring R] (ρ : R →+* Γ(X, ⊤))

include hU in
/-- A finite intersection ring over R makes its coherent sections finite over R. -/
theorem coherentAffineCover_intersection_finite_base (n : ℕ) (a : Fin (n + 1) → ι) :
    let σ := (X.presheaf.map (V U n a).leTop.op).hom.comp ρ
    letI _ringModule := Module.compHom Γ(X, V U n a) σ
    letI _sectionModule := Module.compHom (M.val.obj (op (V U n a))) σ
    Module.Finite R Γ(X, V U n a) →
      Module.Finite R (M.val.obj (op (V U n a))) := by
  let σ := (X.presheaf.map (V U n a).leTop.op).hom.comp ρ
  let _ringModule := Module.compHom Γ(X, V U n a) σ
  let _sectionModule := Module.compHom (M.val.obj (op (V U n a))) σ
  let _tower : IsScalarTower R Γ(X, V U n a) (M.val.obj (op (V U n a))) :=
    SMul.comp.isScalarTower σ
  change Module.Finite R Γ(X, V U n a) →
    Module.Finite R (M.val.obj (op (V U n a)))
  intro h
  let _finiteRing := h
  let _finiteSections := coherentAffineCover_intersection_finite M U hU n a
  exact Module.Finite.trans Γ(X, V U n a) (M.val.obj (op (V U n a)))

variable [Finite ι] [IsNoetherianRing R] (hCover : iSup U = ⊤)

include hU hCover in
/-- The precise additional hypothesis for 12a is base-finite intersection sections. -/
theorem coherentAffineCover_moduleH_finite_of_sections (n : ℕ) :
    letI _cohomologyModule := Module.compHom (ModuleH M n) ρ
    letI _sectionModule := fun a : Fin (n + 1) → ι ↦
      Module.compHom (M.val.obj (op (V U n a)))
        ((X.presheaf.map (V U n a).leTop.op).hom.comp ρ)
    (∀ a : Fin (n + 1) → ι, Module.Finite R (M.val.obj (op (V U n a)))) →
      Module.Finite R (ModuleH M n) := by
  let _cohomologyModule := Module.compHom (ModuleH M n) ρ
  let _sectionModule := fun a : Fin (n + 1) → ι ↦
    Module.compHom (M.val.obj (op (V U n a)))
      ((X.presheaf.map (V U n a).leTop.op).hom.comp ρ)
  intro h
  exact affineCoverModuleH_finite M U ρ hU hCover n (finiteCechRingTerm_finite M U ρ n h)

include hU hCover in
/-- Finiteness of all degree-n intersection rings is a sufficient extra hypothesis. -/
theorem coherentAffineCover_moduleH_finite_of_rings (n : ℕ) :
    letI _cohomologyModule := Module.compHom (ModuleH M n) ρ
    letI _ringModule := fun a : Fin (n + 1) → ι ↦
      Module.compHom Γ(X, V U n a) ((X.presheaf.map (V U n a).leTop.op).hom.comp ρ)
    (∀ a : Fin (n + 1) → ι, Module.Finite R Γ(X, V U n a)) →
      Module.Finite R (ModuleH M n) := by
  let _cohomologyModule := Module.compHom (ModuleH M n) ρ
  let _ringModule := fun a : Fin (n + 1) → ι ↦
    Module.compHom Γ(X, V U n a) ((X.presheaf.map (V U n a).leTop.op).hom.comp ρ)
  intro h
  exact coherentAffineCover_moduleH_finite_of_sections M U hU ρ hCover n
    (fun a ↦ coherentAffineCover_intersection_finite_base M U hU ρ n a (h a))

end FLT.Mazur.FCurve
