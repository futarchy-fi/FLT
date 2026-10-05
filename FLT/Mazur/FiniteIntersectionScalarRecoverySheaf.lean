/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionProjectionSheaf
public import FLT.Mazur.FiniteIntersectionScalarRecoverySections

/-!
# Recovering the original cocycle sheaf

Recovery of the tensor-coordinate units identifies the pulled-back scalar
model sheaf with the original cocycle sheaf on the covered scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
  (p : X ⟶ Spec (.of A)) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤) (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj a)
  (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
    (affineScalarExtensionHom (S := A) (D.map f).hom) =
    ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom)

variable
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ⋙
    Scheme.forget).IsLocallyDirected]

variable
  (g : Cocycle U)
  (z : ∀ s, IntersectionPair s → ((affineIntersectionScalarExtension (A := A) D).obj s)ˣ)
  (hnat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
    ((affineIntersectionScalarExtension (A := A) D).map f).hom (z s k) =
      (z t (intersectionPairMap f k) : (affineIntersectionScalarExtension (A := A) D).obj t))
  (hmul : ∀ s (k : IntersectionTriple s),
    z s (k.1, k.2.1) * z s (k.2.1, k.2.2) = z s (k.1, k.2.2))
  (hz : ∀ s k, e s (z s k : (affineIntersectionScalarExtension (A := A) D).obj s) =
    (finiteIntersectionCocycleUnit U p g s k : (finiteIntersectionSectionDiagram U p).obj s))

include hz in
/-- The recovered inverse-image transition agrees with the original on every subopen. -/
theorem finiteIntersectionScalarRecovery_inverseImageUnit (i j : ι) (V : X.Opens)
    (hi : V ≤ (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv ⁻¹ᵁ
      intersectionColimitOpen
        (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
        (singletonChartSet i))
    (hj : V ≤ (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv ⁻¹ᵁ
      intersectionColimitOpen
        (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
        (singletonChartSet j)) :
    ((affineIntersectionModelCocycle
      (affineIntersectionScalarExtension (A := A) D) z hnat hmul).inverseImage
        (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv).unit i j V hi hj =
      g.unit i j V (by simpa using hi) (by simpa using hj) := by
  let s := pairChartSet i j
  have his : i ∈ s.val := by simp [s]
  have hjs : j ∈ s.val := by simp [s]
  have hV : V ≤ finiteIntersectionOpen U s := by
    simpa only [s, pairChartSet, finiteIntersectionOpen_union,
      finiteIntersectionOpen_singleton] using le_inf (show V ≤ U i by simpa using hi)
        (show V ≤ U j by simpa using hj)
  apply Units.ext
  rw [Cocycle.inverseImage, Cocycle.inverseImageUnit_eq _ _ i j V hi hj
    (intersectionColimitOpen
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s)
    (intersectionColimitOpen_le_singleton _ s i his)
    (intersectionColimitOpen_le_singleton _ s j hjs)
    (hV.trans (le_of_eq
      (finiteIntersectionScalarColimitIso_inv_preimage U p hU hcover D e he s).symm))]
  rw [affineIntersectionModelCocycle_unit_eq _ z hnat hmul i j _ _ _ s his hjs le_rfl]
  change (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv.appLE _ _ _
    (res le_rfl (affineIntersectionColimitSectionEquiv _ s _)) = _
  rw [res_self, finiteIntersectionScalarColimitIso_sectionToOpen U p hU hcover D e he s V hV, hz]
  change res hV ((finiteIntersectionSectionEquiv U p s).symm
    (finiteIntersectionSectionEquiv U p s
      (g.unit i j (finiteIntersectionOpen U s)
        (finiteIntersectionOpen_le_chart U s ⟨i, his⟩)
        (finiteIntersectionOpen_le_chart U s ⟨j, hjs⟩) : Γ(X, finiteIntersectionOpen U s)))) = _
  rw [RingEquiv.symm_apply_apply]
  exact g.natural _ _ _ _ _

/-- The actual pullback along inverse scalar recovery is the original cocycle sheaf. -/
def finiteIntersectionScalarRecoverySheafIso :
    (Scheme.Modules.pullback (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv).obj
        (affineIntersectionModelSheaf (affineIntersectionScalarExtension (A := A) D) z hnat hmul) ≅
      g.sheaf :=
  (affineIntersectionModelCocycle _ z hnat hmul).pullbackIso _
    (intersectionColimitOpen_singleton_cover _) ≪≫
      Cocycle.sheafIsoOfUnits _ g
        (fun i ↦ by simp)
        (finiteIntersectionScalarRecovery_inverseImageUnit U p hU hcover D e he g z hnat hmul hz)

variable [((affineIntersectionSchemeDiagram D) ⋙ Scheme.forget).IsLocallyDirected]

/-- Pullback of the coefficient-model sheaf recovers the original cocycle sheaf. -/
def finiteIntersectionModelColimitSheafIso
    (y : ∀ s, IntersectionPair s → (D.obj s)ˣ)
    (ynat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
      (D.map f).hom (y s k) = (y t (intersectionPairMap f k) : D.obj t))
    (ymul : ∀ s (k : IntersectionTriple s),
      y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))
    (hy : ∀ s k, e s (1 ⊗ₜ[S] (y s k : D.obj s)) =
      (finiteIntersectionCocycleUnit U p g s k : (finiteIntersectionSectionDiagram U p).obj s)) :
    (Scheme.Modules.pullback ((finiteIntersectionScalarColimitIso U p hU hcover D e he).inv ≫
        colimMap (affineIntersectionProjection (A := A) D))).obj
        (affineIntersectionModelSheaf D y ynat ymul) ≅ g.sheaf :=
  ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv).mapIso
      (affineIntersectionProjectionSheafIso D y ynat ymul) ≪≫
    finiteIntersectionScalarRecoverySheafIso U p hU hcover D e he g
      (scalarIntersectionUnit D y) (scalarIntersectionUnit_naturality D y ynat)
      (scalarIntersectionUnit_mul D y ymul) hy

end FLT.Mazur.Approximation
