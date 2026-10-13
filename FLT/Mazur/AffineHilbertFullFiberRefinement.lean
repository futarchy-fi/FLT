/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberInterior
public import FLT.Mazur.AffineHilbertTranslationAdmissibilityDetection

/-!
# Full-fiber domains under actual varying translation refinements

Pulling back the source and changing the independent translation preserves
all previously full fibers. Surjective translation changes detect full fibers
pointwise, not merely admissibility of previously supplied coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "A₁" => translationSource f d b k
local notation "u" => translationSourceMap f d b k
local notation "l" => translationSourceChart f d b k
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "j'" => Over.Hom.left (toEnvelope f hL d W c' l)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "π'" => Over.Hom.left (prod.fst : prod A₁ W ⟶ A₁)

/-- Every old full fiber remains full on the genuinely changed source and translation. -/
theorem translationSource_fullFiber_mono :
    (u).left ⁻¹' fullEnvelopeLocus f hL d V c k ⊆ fullEnvelopeLocus f hL d W c' l := by
  intro x hx
  apply (mem_fullFiberLocus π' (j').opensRange x).mpr
  intro y hy
  have hp : π ((prod.map u b).left y) = (u).left x := by
    change ((prod.map u b).left ≫ π) y = _
    rw [← Over.comp_left, prod.map_fst]
    change (u).left (π' y) = (u).left x
    rw [hy]
  obtain ⟨z, hz⟩ := (mem_fullFiberLocus π (j).opensRange _).mp hx _ hp
  obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
    (translationSourceEnvelope_schemeIsPullback f hL d b c k) z y hz
  exact ⟨a, ha⟩

/-- Surjective translations detect fullness at each original fiber, with all residue branches. -/
theorem translationSource_fullFiber_eq [Surjective b.left] :
    fullEnvelopeLocus f hL d W c' l = (u).left ⁻¹' fullEnvelopeLocus f hL d V c k := by
  apply Set.Subset.antisymm _ (translationSource_fullFiber_mono f hL d b c k)
  intro x hx
  apply (mem_fullFiberLocus π (j).opensRange ((u).left x)).mpr
  intro y hy
  obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_prod_fst_with_id u V).map (Over.forget _)) x y hy.symm
  change (prod.fst : prod A₁ V ⟶ A₁).left z = x at hzx
  change (prod.map u (𝟙 V)).left z = y at hzy
  let g := (prod.map (𝟙 A₁) b).left
  let _ : Surjective g := MorphismProperty.of_isPullback
    ((translationProductRight_isPullback (B := A₁) b).map (Over.forget _))
    (inferInstanceAs (Surjective b.left))
  obtain ⟨w, hw⟩ := g.surjective z
  have hwx : π' w = x := by
    have hh := congrArg (fun t => (prod.fst : prod A₁ V ⟶ A₁).left t) hw
    change (g ≫ (prod.fst : prod A₁ V ⟶ A₁).left) w = _ at hh
    change ((prod.map (𝟙 A₁) b ≫ prod.fst).left) w = _ at hh
    rw [prod.map_fst, Category.comp_id] at hh
    exact hh.trans hzx
  obtain ⟨a, ha⟩ := (mem_fullFiberLocus π' (j').opensRange x).mp hx w hwx
  refine ⟨(translationSourceRelationMap f hL d b c k).left a, ?_⟩
  change ((translationSourceRelationMap f hL d b c k ≫ toEnvelope f hL d V c k).left) a = y
  rw [translationSourceEnvelope_square]
  change (prod.map u b).left ((j') a) = y
  rw [ha]
  have hm : prod.map u b = prod.map (𝟙 A₁) b ≫ prod.map u (𝟙 V) := by
    apply prod.hom_ext <;> simp
  rw [hm]
  change (prod.map u (𝟙 V)).left (g w) = y
  rw [hw, hzy]

/-- Actual translation refinements preserve the maximal OPEN full-envelope neighborhoods. -/
theorem translationSource_fullInterior_mono :
    (u).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k ≤
      fullEnvelopeInterior f hL d W c' l := by
  apply interior_maximal _ ((u).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k).isOpen
  intro x hx
  apply translationSource_fullFiber_mono f hL d b c k
  change (u).left x ∈ fullEnvelopeLocus f hL d V c k
  exact interior_subset hx

/-- An open surjective translation detects the maximal open domain exactly. -/
theorem translationSource_fullInterior_eq [Surjective b.left]
    (hu : IsOpenMap (u).left) :
    fullEnvelopeInterior f hL d W c' l =
      (u).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k := by
  apply SetLike.coe_injective
  change interior (fullEnvelopeLocus f hL d W c' l) =
    (u).left ⁻¹' interior (fullEnvelopeLocus f hL d V c k)
  rw [translationSource_fullFiber_eq,
    hu.preimage_interior_eq_interior_preimage (u).left.continuous]

end FLT.Mazur.HilbertChart.AffineRestriction
