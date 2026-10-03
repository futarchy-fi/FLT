/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveGenus
public import FLT.Mazur.ProjectiveLineProductCharts

/-!
# Constant functions and zeroth cohomology of the projective line

The two polynomial representatives of a global section agree after Laurent
inversion, forcing both to be constant. The resulting H0 equivalence respects
the specified structure morphism and its canonical coefficient scalars.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ProjectiveLineConstantSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type u) [Field K]
open ProjectiveLine FCurve

theorem polynomial_constant (p q : K[X])
    (h : Polynomial.toLaurent p = LaurentPolynomial.invert (Polynomial.toLaurent q)) :
    p = Polynomial.C (p.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have he := congrArg (fun f ↦ (f : K[T;T⁻¹]).coeff (↑(n + 1))) h
    rw [LaurentPolynomial.invert_apply] at he
    have hnat : (Polynomial.toLaurent p).coeff (↑(n + 1)) = p.coeff (n + 1) := by
      change (Finsupp.mapDomain Nat.castEmbedding p.toFinsupp.coeff)
        (Nat.castEmbedding (n + 1)) = _
      rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective,
        Polynomial.toFinsupp_apply]
    have hz : (Polynomial.toLaurent q).coeff (-↑(n + 1)) = 0 := by
      rw [LaurentPolynomial.coeff_toLaurent]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨m, hm⟩
      change (m : ℤ) = -(n + 1 : ℕ) at hm
      omega
    rw [hnat, hz] at he
    simpa using he

/-- Polynomial coordinates of a global section in either chart. -/
def coordinates (b : Bool) : Γ(scheme K, ⊤) →+* K[X] :=
  (((ProjectiveLineProductCharts.chartCover K).f b).appTop ≫
    (Scheme.ΓSpecIso (.of K[X])).hom).hom

/-- Restriction of a global section agrees in the Laurent intersection. -/
theorem coordinate_overlap (r : Γ(scheme K, ⊤)) :
    Polynomial.toLaurent (coordinates K false r) =
      LaurentPolynomial.invert (Polynomial.toLaurent (coordinates K true r)) := by
  have he := congrArg (fun f ↦ f.appTop ≫ (Scheme.ΓSpecIso (.of K[T;T⁻¹])).hom)
    (overlap_condition K)
  simp only [Scheme.Hom.comp_appTop, Category.assoc] at he
  have hl := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (Polynomial.toLaurent : K[X] →+* K[T;T⁻¹]))
  have hr := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    ((LaurentPolynomial.invert (R := K)).toRingHom.comp Polynomial.toLaurent))
  have hi : overlapRight K = Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert (R := K)).toRingHom.comp Polynomial.toLaurent)) := by
    simp only [overlapRight, inversion_hom, overlapLeft, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hi] at he
  change (left K).appTop ≫ (Spec.map (CommRingCat.ofHom Polynomial.toLaurent)).appTop ≫ _ = _ at he
  rw [hl, hr] at he
  exact congrArg (fun f ↦ f.hom r) he
theorem coordinate_scalar (b : Bool) (a : K) :
    coordinates K b (structureScalarMap (toBase K) a) = Polynomial.C a := by
  have he := congrArg (fun f ↦ (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    (Scheme.ΓSpecIso (.of K[X])).hom) (ProjectiveLineProductCharts.chartCover_toBase K b)
  rw [Scheme.Hom.comp_appTop] at he
  change _ = (Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom Polynomial.C)).appTop ≫ _ at he
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc] at he
  exact congrArg (fun f ↦ f.hom a) he

theorem coordinates_ext {r s : Γ(scheme K, ⊤)}
    (h : ∀ b, coordinates K b r = coordinates K b s) : r = s := by
  apply (ProjectiveLineProductCharts.chartCover K).ext_elem r s
  intro b
  exact (Scheme.ΓSpecIso (.of K[X])).commRingCatIsoToRingEquiv.injective (h b)

theorem constant_sections : HasConstantGlobalSections (toBase K) := by
  constructor
  · intro a b hab
    have he := congrArg (coordinates K false) hab
    rw [coordinate_scalar, coordinate_scalar] at he
    exact Polynomial.C_injective he
  · intro r
    let p := coordinates K false r
    let q := coordinates K true r
    have hov := coordinate_overlap K r
    have hp := polynomial_constant K p q hov
    have hrev : Polynomial.toLaurent q = LaurentPolynomial.invert (Polynomial.toLaurent p) := by
      rw [hov, LaurentPolynomial.involutive_invert]
    have hq := polynomial_constant K q p hrev
    have hc : p.coeff 0 = q.coeff 0 := by
      have he := congrArg (fun f ↦ (f : K[T;T⁻¹]).coeff 0) hov
      rw [LaurentPolynomial.invert_apply, neg_zero] at he
      change (Finsupp.mapDomain Nat.castEmbedding p.toFinsupp.coeff) (Nat.castEmbedding 0) =
        (Finsupp.mapDomain Nat.castEmbedding q.toFinsupp.coeff) (Nat.castEmbedding 0) at he
      simpa only [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective,
        Polynomial.toFinsupp_apply] using he
    refine ⟨p.coeff 0, coordinates_ext K fun b ↦ ?_⟩
    rw [coordinate_scalar]
    cases b
    · exact hp.symm
    · exact (congrArg Polynomial.C hc).trans hq.symm
/-- The actual zeroth cohomology is the coefficient field, with its canonical scalars. -/
def h0Equiv : H0 (toBase K) ≃ₗ[K] K :=
  (scalarH0ConstantsEquiv (toBase K) (constant_sections K)).symm
@[simp] theorem h0Equiv_constants (a : K) :
    h0Equiv K (scalarH0Constants (toBase K) a) = a :=
  (scalarH0ConstantsEquiv (toBase K) (constant_sections K)).symm_apply_apply a
end FLT.Mazur.ProjectiveLineConstantSections
