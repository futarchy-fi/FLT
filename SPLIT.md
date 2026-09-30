# FC08 B20/B21/C25: proof-size review and dispatch split

Checked 2026-09-30 06:44 UTC at `4cc7a4e6`, Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`. This is a field-base plan,
not a plan for arbitrary-base coherent higher direct images. Every listed
implementation leaf is a new `FLT/Mazur/<name>.lean` module. Caps include
headers and documentation. They are hard stop/split limits, not measured
lengths of proofs that do not exist yet.

The ready execution order is **21a, 20a, 21b, 21c**. The apparent reordering
is necessary because 20a uses the all-degree predicate defined by 21a.
Commit this review before any implementation; commit each green module
with its sorted `FLT.lean` import. No push, admitted proofs or new axioms.

## Existing API and ownership evidence

The following are read-only checks, rerunnable in this checkout:

```
rg -n 'theorem|lemma|def ' FLT/Mazur/CoherentGenericRankOneCriterion.lean
rg -n 'moduleScalarH_finite|moduleFinite_of_exact_pair' FLT/Mazur/ModuleCohomologyExact.lean
rg -n 'moduleToSheaf_shortExact' FLT/Mazur/ModuleStalkExact.lean
rg -n 'closedPushforwardScalarHEquiv' FLT/Mazur/ClosedPushforwardCohomology.lean
rg -n 'coherent_moduleH_finite|closedSubscheme_coherent_moduleH_finite' FLT/Mazur/ProjectiveCoherentCohomology.lean
rg -n 'acyclicPushforwardScalarHEquiv|ModulePushforwardAcyclic' FLT/Mazur/AcyclicPushforwardCohomology.lean
rg -n 'unitSheaf_isFinitePresentation' FLT/Mazur/CoherentFreeSheaf.lean
rg -n 'moduleScalarHUnitEquiv' FLT/Mazur/ModuleCohomology.lean
rg -n 'subsingleton_H_of_isZero' .lake/packages/mathlib/Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean
rg -n 'Serre|serre|eventually.*[Zz]ero|eventually.*[Ss]ubsingleton' FLT/Mazur/Projective*.lean
rg -n 'pushforward.*[Qq]uasi|[Qq]uasi.*pushforward' FLT/Mazur/AffinePushforwardQuasicoherent.lean .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Modules
cat ../wt-r1e/BRIEF.md ../wt-r1e/PREV_B17J_BLOCKED.md
cat ../wt-r5a/BRIEF.md ../wt-r5a/PREV_B18J_BLOCKED.md
sed -n '82,110p' ../wt-r5a/PREV_B18I_BLOCKED.md
```

Findings from the declarations and their proofs, not just filenames:

* D19's `generic_rank_one_of_zero` handles arbitrary Noetherian X when
  the zero case is supplied; `generic_rank_one_devissage` assumes nonempty
  X. `HasGenericRankOneWitnesses` quantifies over **every** ideal sheaf J
  with integral subscheme, with support equality, residue annihilation,
  residue dimension one, coherence and the property on the ambient X.
* A2 already proves the four finite exact-sequence degree patterns. The
  missing adapter is their conjunction over all natural degrees and the
  actual forgetful short-exactness theorem. Fixed-degree finiteness alone
  is not a two-out-of-three property.
* B14 supplies the closed **absolute scalar** comparison. This is enough
  for 20a; waiting for B18's relative closed specialization would add an
  unnecessary dependency for our field-only theorem.
* B13 proves finite cohomology of coherent sheaves on polynomial projective
  space and on a specified closed subscheme. It does not prove relative
  Serre vanishing, nor coherence of a non-affine direct image. Existing
  quasi-coherent direct-image results here are for affine morphisms.
* B18's absolute acyclic scalar comparison already exists. Its unfinished
  open/relative comparison and geometric Serre input must not be silently
  replaced by an assumed comparison or assumed higher-image vanishing in
  the eventual proper finiteness theorem.
* The structure module is coherent; `moduleScalarHUnitEquiv` identifies its
  cohomology with actual `ScalarH`, including `H1`.
* C24's `NodalFiberCore`, `NodalGeometricFibers` and `NodalFamilyCore` exist.
  The file explicitly says these are necessary conditions, not the full
  DR stable-genus-one condition. Genus does not discharge the missing
  dualizing-sheaf/Neron-polygon condition.

The proof of Stacks [02O5](https://stacks.math.columbia.edu/tag/02O5) was
also read: it chooses G = pi_*(L^n) on each integral closed Z, then pushes
G to X. Its statement concerns coherent higher direct images. Our
field-only specialization may use absolute cohomology comparisons, but
must still prove coherence of G and existence of an acyclic power.

## Required results from the other lanes (not new hypotheses)

These names label contracts; they are not assertions that matching Lean
identifiers already exist. B17/B18 own their modules; this task does not
edit them or duplicate their ongoing proofs.

**B17-FINAL (rows 10c--13).** For integral Z proper over k, construct its
Chow modification `pi : Z' ⟶ Z`, a dense nonempty `U : Z.Opens`, an
isomorphism over U, a finite-dimensional polynomial projective space and
`i : Z' ⟶ ProjectiveSpace.space k (Fin (m+1))` which is a closed immersion
and commutes with the specified structure maps. Construct the actual
line sheaf `L = pullback i O(1)`, prove local rank one, and give its second
relative very ample presentation for pi. On every affine open V in Z,
that presentation is a closed projective embedding over Γ(Z,V), with
coefficient isomorphisms identifying L and all its natural tensor powers
with the restrictions of O(1) and O(n). Retain pullback/tensor and open
restriction compatibility, including power zero. The dense-open inverse
and the commuting squares are part of the output, not extra assumptions.

**B18-COMP (rows 5c--7).** For `a : Y ⟶ Z`, `M : Y.Modules`, actual
`ModulePushforwardAcyclic a M` implies a natural module isomorphism
`((pushforward g).rightDerived p).obj ((pushforward a).obj M) ≅
 ((pushforward (a ≫ g)).rightDerived p).obj M` for every g and p.
It must commute with open restriction and local scalars and specialize
to the existing absolute scalar comparison and closed immersion comparison.
No extra acyclicity of g or of the composite is allowed.

**B18-SERRE (geometric prerequisite to row 8, still absent).** For the
actual B17 L, prove an eventual bound N such that every n >= N satisfies
`ModulePushforwardAcyclic pi (L^n)` (and simultaneously for g' for the
full row-8 contract). Choose one n satisfying both eventual bounds.
This is a theorem derived from relative ampleness, not a field of an
assumption record. B18's current brief stops at 6b; neither 6b nor the
existing absolute comparison alone supplies this result. Its own
projective/relative Serre proof must be split in that lane before dispatch;
this review does not assign a fictitious <=500-line bound to that port.

## B20: coherent generic-rank-one witnesses

Notation below: `P f M := ∀ q, Module.Finite k (ModuleScalarH f M q)`;
`J : X.IdealSheafData`, `[IsIntegral J.subscheme]`, `j := J.subschemeι`,
`g := j ≫ f`. Write `T n` for the actual natural tensor power of the B17
L, and `G n := (pushforward pi).obj (T n)`. Proposed Lean sketches omit
only implicit universes/instances and use B17's future names schematically.
They do not introduce opaque geometric predicates.

### 20a — ClosedCohomologyFinite (cap 160; READY after 21a)

```
closedPushforward_hasFiniteCohomology_iff
    (j : Z ⟶ X) [IsClosedImmersion j]
    [X.IsSeparated] [IsLocallyNoetherian X]
    (G : Z.Modules) [G.IsFinitePresentation] :
  P f ((pushforward j).obj G) ↔ P (j ≫ f) G
```

Dependency: B14 `closedPushforwardScalarHEquiv`, and 21a. Transfer each
finite instance by the linear equivalence in both directions. This is the
last finiteness transport in 20h; it does not construct rank-one witnesses.

### 20b — ChowWitnessSectionsLocalization (cap 450; waits B17-FINAL)

For every affine V in Z and r in Γ(Z,V), show sections of G n on the
principal open D(r) are localization of sections on V, with the canonical
restriction map as the localization map:

```
IsLocalizedModule (Submonoid.powers r)
  (G n).presheaf.map (homOfLE (D(r) ≤ V)).op
```

Use the finite standard affine cover of pi^-1(V) coming from B17,
quasi-coherence of T n and exactness of module localization on the
finite equalizer computing sections. No proper-coherent-finiteness
circularity. Search anchors: `ProjectiveSpaceCharts`,
`TildePrincipalOpen`, `AffineKernelLocalization`, `PushforwardCech`.
No B18 dependency. This proves a concrete localization assertion for the
Chow coefficient, not general proper pushforward coherence.

### 20c — ChowWitnessAffineCoherence (cap 450; waits 20b, B17-FINAL)

For every affine V in Z, construct the canonical tilde comparison

```
((G n).restrict V.ι) ≅
  (tilde of the Γ(Z,V)-module of sections on pi^-1(V))
```

with the usual V-to-Spec identification. Prove that section module finite
using B13 `closedSubscheme_coherent_moduleH_finite` in degree zero and
`moduleH0Equiv`, with B17's affine relative projective embedding and
coherent T n. Apply `AffineCoherent` to obtain
`((G n).restrict V.ι).IsFinitePresentation`.
20b proves the tilde comparison is invertible; do not merely infer it
from finite global sections. No B18 dependency.

### 20d — ChowWitnessCoherence (cap 180; waits 20c, B17-FINAL)

```
chowPushforwardPower_isFinitePresentation (n : ℕ) :
  (G n).IsFinitePresentation
```

Glue the actual local finite presentations from 20c with
`CoherentOpenDescent`. Establish finite presentation of T n via its local
rank-one trivializations (B17-FINAL). This must precede 20h; the stalk and
cohomology arguments alone cannot prove coherence.

### 20e — ChowWitnessGenericRestriction (cap 450; waits B17-FINAL)

Construct an isomorphism of `(G n).restrict U.ι` with the line sheaf
transported from `(T n).restrict (pi^-1(U)).ι` through B17's isomorphism
of schemes over U. Prove its local rank one and, at the actual generic
point eta of Z,

```
IsLocallyFree (G n restricted to U) of rank 1
Module.finrank (Z.residueField eta) ((G n).presheaf.stalk eta) = 1
```

The second line includes the canonical residue action and its proof of
maximal-ideal annihilation: the local ring of integral Z at eta is a
field. Depend on `ClosedPushforwardRestriction`'s open-square pattern,
`ModuleLineBundlePullback`, `CartierTensorRank`, and the integral generic
stalk API. No B18 dependency. Do not assume generic rank one as input.

### 20f — ChowWitnessFiniteCohomology (cap 300; waits B17-FINAL, B18-SERRE)

```
exists_chow_power_finite : ∃ n : ℕ,
  ModulePushforwardAcyclic pi (T n) ∧ P g (G n)
```

Choose n using B18-SERRE. Apply B13 to the absolute projective embedding
of Z' and T n, retaining `pi ≫ g` as the field structure map. Transfer
finiteness by `acyclicPushforwardScalarHEquiv`. This field-only proof
already has its absolute B18 comparison; it need not wait for a new
relative comparison once the geometric acyclicity theorem exists.
B18 row 8 may supply a stronger conclusion, including positive vanishing.

### 20g — ChowWitnessClosedStalk (cap 450; waits 20d, 20e)

For F n := j_*(G n), prove the exact three geometric fields needed by D19:

```
support (F n) = Set.range j
StalkAnnihilated (F n) (j (genericPoint J.subscheme))
letI := residueModule (F n) _ hAnn
Module.finrank (X.residueField (j (genericPoint J.subscheme)))
  ((F n).presheaf.stalk (j (genericPoint J.subscheme))) = 1
```

Use the closed-immersion stalk and residue-field comparisons, 20e, and
closed coherent support: containing the generic point implies containing
its entire closed irreducible image. Coherence comes from 20d and
`closedPushforward_isFinitePresentation`. Search anchors:
`CoherentClosedPushforward`, `CoherentSupport`, `GenericIdealSupport`,
`CoherentGenericCoordinates`, `IntegralClosedSupport`. No further B18
requirement beyond the transitive need to select a power in 20h.

### 20h — ProperCohomologyWitnesses (cap 240; waits 20a,20d,20f,20g)

```
proper_hasGenericRankOneWitnesses
    (f : X ⟶ Spec (.of k)) [IsProper f] :
  CoherentDevissage.HasGenericRankOneWitnesses (P f)
```

Derive Noetherian/separated instances from properness over a field. For
**each** J with integral subscheme apply the preceding construction to g,
choose n from 20f and package `j_*(G n)` with all D19 fields. Use 20a for
its finite cohomology. No witness or higher-cohomology finiteness remains
an input. This is the actual completion of B20.

## B21: devissage and the structure sheaf

### 21a — CoherentCohomologyFinite (cap 180; READY)

Define `HasFiniteCohomology f M := P f M`. Prove

```
hasFiniteCohomology_twoOutOfThree (f) :
  CoherentDevissage.TwoOutOfThree (HasFiniteCohomology f)
hasFiniteCohomology_of_isZero (f) (M) (hM : IsZero M) : P f M
hasFiniteCohomology_iso (f) (e : M ≅ N) : P f M ↔ P f N
```

Dependencies: A1/A2 `ModuleCohomologyExact`, D19's predicate structure,
`moduleToSheaf_shortExact`, and Mathlib's `subsingleton_H_of_isZero`.
Handle the left degree-zero endpoint separately; successor degrees use
the preceding quotient degree. Zero and iso results will support the
empty scheme case and coefficient comparisons without geometric inputs.
No B17/B18 dependency and no Noetherian hypothesis is needed for this leaf.

### 21b — CoherentCohomologyDevissage (cap 140; READY after 21a)

```
coherent_hasFiniteCohomology_of_witnesses [IsNoetherian X]
  (hw : HasGenericRankOneWitnesses (HasFiniteCohomology f))
  (M : X.Modules) [M.IsFinitePresentation] : HasFiniteCohomology f M
```

Use `generic_rank_one_of_zero` and the zero theorem from 21a. Also give
the empty-scheme conclusion without hw, using stalk detection of zero.
No nonempty assumption. This is an explicitly conditional assembly
lemma, **not** proper finiteness. D19 + 21a are sufficient; no B17/B18.

### 21c — StructureCohomologyFinite (cap 120; READY after 21b)

```
finiteDimensional_scalarH_of_witnesses [IsNoetherian X]
  (hw : HasGenericRankOneWitnesses (HasFiniteCohomology f)) (q : ℕ) :
  FiniteDimensional k (ScalarH f q)
finiteDimensional_H1_of_witnesses [IsNoetherian X] (hw : ...) :
  FiniteDimensional k (H1 f)
```

Use `unitSheaf_isFinitePresentation`, 21b and `moduleScalarHUnitEquiv`.
No B17/B18 dependency. The theorem name and documentation retain the
witness hypothesis. No genus is defined from this conditional theorem.

### 21d — ProperCoherentCohomology (cap 180; waits 20h,21b,21c)

```
proper_coherent_hasFiniteCohomology (f) [IsProper f]
  (M : X.Modules) [M.IsFinitePresentation] : HasFiniteCohomology f M
finiteDimensional_H1_of_proper (f) [IsProper f] :
  FiniteDimensional k (H1 f)
```

Derive all Noetherian instances, feed 20h into 21b/21c, including empty X.
Neither witnesses, finite H1, nor a substitute vector space are allowed
as extra assumptions. This is B21 completion, transitively blocked by
B17-FINAL and B18-SERRE (or completed B18 row 8).

## C25: genus endpoint

### 25a — ProperCurveGenus (cap 120; waits 21d)

For actual `f : X ⟶ Spec (.of k)`, `[IsProper f]`,
`hd : topologicalKrullDim X = 1`, and `hc : HasConstantGlobalSections f`,
define `curveGenus f hd hc := Module.finrank k (H1 f)` with the **proved**
`finiteDimensional_H1_of_proper f` installed in the definition. Prove the
unfolding equation and independence of proof arguments. Retain the
explicit constant-sections condition; do not derive it without 0BUG.
No integral or smooth hypothesis, no assumed finite-dimensionality.
Search anchors: `CurveGenus`, `ScalarCohomology`; existing `CurveGenus`
only addresses H0 and has no actual genus definition.

### 25b — NodalGeometricFiberGenus (cap 200; waits 25a and existing C24)

Define a necessary genus-one fiber condition on a proper f: for every
algebraically closed L, point s and pullback square `(fst,snd)`, require
`NodalFiberCore snd`, `HasConstantGlobalSections snd`, and
`curveGenus snd hd hc = 1`. Derive properness of snd from the square and
dimension one from nonempty + pure dimension one; do not ask for an
unrelated whole-space dimension as replacement for purity. Prove its
canonical-pullback specialization. If the purity-to-dimension bridge
cannot fit this cap, split that bridge before implementation.

This is a **necessary genus-one nodal fiber contract**, not a definition
of DR stability: retain the existing dualizing/Neron-polygon gap. No
field-extension comparison or arbitrary-base R1 theorem is included.
Dependencies: B17/B18 transitively through 21d and 25a; existing C22--24.

## Completion checks

Each ready module: foreground `lake build FLT.Mazur.<module>`, followed
by `lake exe runLinter FLT.Mazur.<module>` alone. Check root coverage via
`lake build +FLT:olean` after the final import; do not lint FLT globally.
Scan only new sources for admitted proofs/new axioms and verify the stated
line caps. Use `#print axioms` on exported assembly results. Preserve the
inherited untracked briefs. The final handoff names local commits and the
blocked leaves; it must not label B20/B21/C25 complete.
