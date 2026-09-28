/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FCurveContracts
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Affine charts for effective Cartier divisors

The predicate `EffectiveCartier` uses quasi-coherent ideal sheaf data and regular
local equations. A chart can be shrunk to an affine open, and equations transport
across open immersions. Thus the predicate is local on any open cover.
Multiplication of ideals gives addition of divisors, including multiplicities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X Y : Scheme.{u}}

/-- An affine chart on which the ideal has one regular generator. -/
def CartierChart (I : X.IdealSheafData) (U : X.affineOpens) : Prop :=
  ∃ a : Γ(X, U), IsRegular a ∧ I.ideal U = Ideal.span {a}

private lemma regular_map_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {a : R} (ha : IsRegular a) : IsRegular (f a) := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  rw [← isLeftRegular_iff_isRegular]
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
    (Module.Flat.isSMulRegular_of_isRegular (M := S) ha)

/-- Regular equations restrict to smaller affine opens. -/
lemma CartierChart.mono {I : X.IdealSheafData} {U V : X.affineOpens}
    (hV : CartierChart I V) (hUV : U ≤ V) : CartierChart I U := by
  obtain ⟨a, ha, hI⟩ := hV
  let f := (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom
  have hf : f.Flat := by
    simpa [Scheme.Hom.appLE] using Scheme.Hom.flat_appLE (𝟙 X) V.2 U.2 hUV
  refine ⟨f a, regular_map_of_flat f hf ha, ?_⟩
  rw [← I.map_ideal hUV, hI, Ideal.map_span, Set.image_singleton]
  rfl

/-- A chart on an open subscheme is the same chart on its image. -/
lemma cartierChart_comap_iff (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) :
    CartierChart (I.comap f) U ↔
      CartierChart I ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩ := by
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  have he : (I.comap f).ideal U =
      (I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩).map e.toRingHom := by
    rw [I.ideal_comap_of_isOpenImmersion]
    exact (Ideal.map_comap_of_equiv e).symm
  constructor
  · rintro ⟨a, ha, hI⟩
    refine ⟨e.symm a, regular_map_of_flat _ (.of_bijective e.symm.bijective) ha, ?_⟩
    have h := congrArg (Ideal.map e.symm.toRingHom) (he.symm.trans hI)
    simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv,
      Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom] using h
  · rintro ⟨a, ha, hI⟩
    refine ⟨e a, regular_map_of_flat _ (.of_bijective e.bijective) ha, ?_⟩
    rw [he, hI, Ideal.map_span, Set.image_singleton]
    rfl

/-- The local equation can be chosen inside any prescribed open neighborhood. -/
lemma EffectiveCartier.exists_chart_le {I : X.IdealSheafData} (hI : EffectiveCartier I)
    {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧ CartierChart I U := by
  obtain ⟨V, hxV, hV⟩ := hI x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V.1 ⊓ W from ⟨hxV, hx⟩)
      (V.1 ⊓ W).isOpen
  exact ⟨⟨U, hU⟩, hxU, le_trans hUV inf_le_right,
    CartierChart.mono (U := ⟨U, hU⟩) hV (show U ≤ V.1 from hUV.trans inf_le_left)⟩

/-- On every affine open, regular equations exist on a cover by principal opens.
This does not ask that the ideal on the whole affine open be principal. -/
theorem effectiveCartier_iff_basicOpen (I : X.IdealSheafData) :
    EffectiveCartier I ↔ ∀ (U : X.affineOpens) (x : X), x ∈ U.1 →
      ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧ CartierChart I (X.affineBasicOpen f) := by
  constructor
  · intro hI U x hx
    obtain ⟨V, hxV, hV⟩ := hI x
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hx, hxV⟩
    exact ⟨f, hxf, CartierChart.mono hV (hfg.trans_le (X.basicOpen_le g))⟩
  · intro h x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨f, hxf, hf⟩ := h ⟨U, hU⟩ x hxU
    exact ⟨X.affineBasicOpen f, hxf, hf⟩

/-- For an affine scheme, localize its actual global ideal on principal neighborhoods.
The generator may differ between these neighborhoods. -/
theorem effectiveCartier_iff_affine [IsAffine X] (I : X.IdealSheafData) :
    EffectiveCartier I ↔ ∀ x : X, ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧
      ∃ a : Γ(X, X.basicOpen f), IsRegular a ∧
        (Scheme.IdealSheafData.equivOfIsAffine I).map
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = Ideal.span {a} := by
  have hmap (f : Γ(X, ⊤)) :
      (Scheme.IdealSheafData.equivOfIsAffine I).map
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
        I.ideal (X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) f) :=
    I.map_ideal_basicOpen ⟨⊤, isAffineOpen_top X⟩ f
  simp only [hmap]
  constructor
  · intro h x
    exact (effectiveCartier_iff_basicOpen I).mp h ⟨⊤, isAffineOpen_top X⟩ x trivial
  · rintro h x
    obtain ⟨f, hxf, hf⟩ := h x
    exact ⟨X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) f, hxf, hf⟩

/-- Cartier divisors restrict along any open immersion. -/
lemma EffectiveCartier.comap_of_isOpenImmersion {I : Y.IdealSheafData}
    (hI : EffectiveCartier I) (f : X ⟶ Y) [IsOpenImmersion f] :
    EffectiveCartier (I.comap f) := by
  intro x
  obtain ⟨V, hxV, hV, hIV⟩ := hI.exists_chart_le
    (show f x ∈ f.opensRange from ⟨x, rfl⟩)
  let U := (IsOpenImmersion.affineOpensEquiv f).symm ⟨V, hV⟩
  refine ⟨U, hxV, (cartierChart_comap_iff I f U).mpr ?_⟩
  have he : (IsOpenImmersion.affineOpensEquiv f U).1 = V :=
    congrArg Subtype.val ((IsOpenImmersion.affineOpensEquiv f).apply_symm_apply ⟨V, hV⟩)
  change CartierChart I (IsOpenImmersion.affineOpensEquiv f U).1
  rw [he]
  exact hIV

/-- Restriction detects exactly the local Cartier condition at points of the open. -/
theorem effectiveCartier_restrict_iff (I : X.IdealSheafData) (W : X.Opens) :
    EffectiveCartier (I.comap W.ι) ↔
      ∀ x ∈ W, ∃ U : X.affineOpens, x ∈ U.1 ∧ CartierChart I U := by
  constructor
  · intro h x hx
    obtain ⟨U, hxU, hU⟩ := h ⟨x, hx⟩
    refine ⟨⟨W.ι ''ᵁ U, U.2.image_of_isOpenImmersion W.ι⟩, ?_,
      (cartierChart_comap_iff I W.ι U).mp hU⟩
    exact ⟨⟨x, hx⟩, hxU, rfl⟩
  · intro h x
    obtain ⟨V, hxV, hV⟩ := h x.1 x.2
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x.1 ∈ V.1 ⊓ W from ⟨hxV, x.2⟩) (V.1 ⊓ W).isOpen
    let U' : W.toScheme.affineOpens :=
      (affineOpensRestrict W).symm ⟨⟨U, hU⟩, le_trans hUV inf_le_right⟩
    refine ⟨U', hxU, (cartierChart_comap_iff I W.ι U').mpr ?_⟩
    have he : (affineOpensRestrict W U').1 = ⟨U, hU⟩ :=
      congrArg Subtype.val ((affineOpensRestrict W).apply_symm_apply _)
    change CartierChart I (affineOpensRestrict W U').1
    rw [he]
    exact CartierChart.mono (U := ⟨U, hU⟩) hV (show U ≤ V.1 from hUV.trans inf_le_left)

/-- The Cartier condition can be checked on any open cover. -/
theorem effectiveCartier_iff_openCover (I : X.IdealSheafData) (C : X.OpenCover) :
    EffectiveCartier I ↔ ∀ i, EffectiveCartier (I.comap (C.f i)) := by
  refine ⟨fun h i ↦ h.comap_of_isOpenImmersion _, ?_⟩
  intro h x
  obtain ⟨y, hy⟩ := C.covers x
  obtain ⟨U, hyU, hU⟩ := h (C.idx x) y
  refine ⟨⟨C.f (C.idx x) ''ᵁ U, U.2.image_of_isOpenImmersion _⟩, ?_,
    (cartierChart_comap_iff I (C.f (C.idx x)) U).mp hU⟩
  exact ⟨y, hyU, hy⟩

/-- In particular it suffices to check the restrictions to all affine opens. -/
theorem effectiveCartier_iff_affine_restrict (I : X.IdealSheafData) :
    EffectiveCartier I ↔ ∀ U : X.affineOpens, EffectiveCartier (I.comap U.1.ι) := by
  constructor
  · exact fun h U ↦ h.comap_of_isOpenImmersion U.1.ι
  · intro h x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (effectiveCartier_restrict_iff I U).mp (h ⟨U, hU⟩) x hxU

/-- The unit ideal is the empty divisor, with local equation one. -/
lemma cartierChart_top (U : X.affineOpens) : CartierChart (⊤ : X.IdealSheafData) U := by
  exact ⟨1, isRegular_one, (Ideal.span_singleton_one).symm⟩

/-- The empty divisor is effective Cartier on every scheme, including the empty scheme. -/
theorem effectiveCartier_top : EffectiveCartier (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU, cartierChart_top _⟩

/-- The multiplicative identity for ideal sheaves represents the empty divisor. -/
theorem effectiveCartier_one : EffectiveCartier (1 : X.IdealSheafData) :=
  effectiveCartier_top

/-- The subscheme of the unit ideal has no points. -/
theorem isEmpty_top_subscheme : IsEmpty (⊤ : X.IdealSheafData).subscheme :=
  inferInstance

/-- On a common chart, multiplication of ideals multiplies their regular equations. -/
lemma CartierChart.mul {I J : X.IdealSheafData} {U : X.affineOpens}
    (hI : CartierChart I U) (hJ : CartierChart J U) : CartierChart (I * J) U := by
  obtain ⟨a, ha, hIa⟩ := hI
  obtain ⟨b, hb, hJb⟩ := hJ
  refine ⟨a * b, ha.mul hb, ?_⟩
  change I.ideal U * J.ideal U = _
  rw [hIa, hJb, Ideal.span_singleton_mul_span_singleton]

/-- Absolute sums of effective Cartier divisors are effective Cartier. -/
theorem EffectiveCartier.mul {I J : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) : EffectiveCartier (I * J) := by
  intro x
  obtain ⟨V, hxV, hV⟩ := hI x
  obtain ⟨U, hxU, hUV, hU⟩ := hJ.exists_chart_le hxV
  exact ⟨U, hxU, (CartierChart.mono hV hUV).mul hU⟩

/-- Repetition retains multiplicities through powers of the ideal. -/
theorem EffectiveCartier.pow {I : X.IdealSheafData} (hI : EffectiveCartier I) (n : ℕ) :
    EffectiveCartier (I ^ n) := by
  induction n with
  | zero => simpa using effectiveCartier_one (X := X)
  | succ n hn => simpa only [pow_succ] using hn.mul hI

/-- A finite sum of effective Cartier divisors, represented by the product of ideals. -/
theorem effectiveCartier_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, EffectiveCartier (I i)) : EffectiveCartier (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using effectiveCartier_one (X := X)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hI i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj ↦ hI j (Finset.mem_insert_of_mem hj)))

/-- The actual closed subscheme recovers the ideal used in the Cartier predicate. -/
theorem effectiveCartier_ker_subschemeι_iff (I : X.IdealSheafData) :
    EffectiveCartier I.subschemeι.ker ↔ EffectiveCartier I := by
  rw [I.ker_subschemeι]

/-- On a Cartier chart, the closed immersion has the prescribed principal kernel. -/
lemma CartierChart.ker_eq {I : X.IdealSheafData} {U : X.affineOpens}
    (hI : CartierChart I U) :
    ∃ a : Γ(X, U), IsRegular a ∧
      RingHom.ker (I.subschemeι.app U).hom = Ideal.span {a} := by
  simpa only [I.ker_subschemeι_app U] using (show ∃ a, IsRegular a ∧
    I.ideal U = Ideal.span {a} from hI)

/-- The sections of the divisor on an affine chart form the quotient by its ideal. -/
noncomputable def cartierChartQuotientIso (I : X.IdealSheafData) (U : X.affineOpens)
    (a : Γ(X, U)) (ha : I.ideal U = Ideal.span {a}) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅ CommRingCat.of (Γ(X, U) ⧸ Ideal.span {a}) :=
  I.subschemeObjIso U ≪≫ eqToIso (by rw [ha])

end FLT.Mazur.FCurve
