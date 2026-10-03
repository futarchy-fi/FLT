/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointStructureCohomology
public import FLT.Mazur.ModuleCohomologyVanishing
public import FLT.Mazur.ProjectiveLineCohomologyVanishing
public import FLT.Mazur.PolygonPinchingDiagram
/-!
# Positive structure cohomology of scheme coproducts

The component inclusions give a disjoint cover. Transport the component
cohomology through their open-range isomorphisms, then apply the disjoint-cover
comparison. The final theorem uses the specified normalization coproduct.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.SchemeCoproductCohomology
open FCurve
/-- Transport structure-cohomology vanishing through a scheme isomorphism. -/
theorem of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (r : ℕ)
    (h : Subsingleton (ModuleH (structureUnitModule X) r)) :
    Subsingleton (ModuleH (structureUnitModule Y) r) := by
  have := h
  have hz : Subsingleton (ModuleH ((structureUnitModule X).restrict e.inv) r) :=
    (moduleHIsoEquiv e.symm (structureUnitModule X) r).surjective.subsingleton
  exact (moduleHIsoOfIso (Scheme.Modules.restrictUnitIso e.inv) r).surjective.subsingleton
/-- A coproduct of acyclic schemes has vanishing positive structure cohomology. -/
theorem scheme_positive {ι : Type} [LinearOrder ι] (X : ι → Scheme.{u})
    (hX : ∀ i q, Subsingleton (ModuleH (structureUnitModule (X i)) (q + 1))) (q : ℕ) :
    Subsingleton (ModuleH (structureUnitModule (∐ X)) (q + 1)) := by
  let U : ULift.{u} ι → (∐ X).Opens := fun i ↦ (Sigma.ι X i.down).opensRange
  have hd : Pairwise (fun i j ↦ Disjoint (U i) (U j)) := by
    intro i j hij
    exact disjoint_opensRange_sigmaι X i.down j.down (fun e ↦ hij (ULift.ext e))
  have hc : iSup U = ⊤ := by
    simpa [U] using (sigmaOpenCover X).iSup_opensRange
  apply DisjointStructureCohomology.positive U hd hc
  intro i r
  have hz := of_iso (Sigma.ι X i.down).isoOpensRange (r + 1) (hX i.down r)
  have := hz
  exact moduleH_subsingleton_of_iso (Scheme.Modules.restrictUnitIso (U i).ι) (r + 1)
/-- The actual normalization coproduct has no positive structure cohomology. -/
theorem components_positive (K : Type u) [Field K] (n q : ℕ) :
    Subsingleton (ModuleH (structureUnitModule (PolygonPinching.components K n).left) (q + 1)) := by
  let e : (∐ fun _ : Fin n ↦ (PolygonPinching.component K).left) ≅
      (PolygonPinching.components K n).left :=
    asIso (sigmaComparison (Over.forget (Spec (.of K)))
      (fun _ : Fin n ↦ PolygonPinching.component K))
  apply of_iso e (q + 1)
  exact scheme_positive _ (fun _ r ↦ ProjectiveLineCohomologyVanishing.structure_positive K r) q
end FLT.Mazur.SchemeCoproductCohomology
