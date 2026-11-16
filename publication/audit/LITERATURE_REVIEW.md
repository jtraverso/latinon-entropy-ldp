# Bibliographic gate — scoped review, 15 November 2026

Verdict: **PASS_SCOPED_BIBLIOGRAPHIC_REVIEW**.

This records source checks and defensible positioning. It is not an exhaustive
absence proof for earlier results or a substitute for a specialist's priority
review. No numerical journal-level rating is used as evidence.

## Primary sources examined

- Garbe–Hancock–Hladký–Sharifzadeh, *Limits of Latin squares*, Discrete Analysis
  2023:8, DOI 10.19086/da.83253, arXiv:2010.07854v3. Definitions 3.16 and 4.3
  match the measure representation and full distance; Theorems 3.13 and 4.7
  supply compactness and the convergence framework. Section 12.2 discusses
  entropy and counting. The manuscript fixes Ent = −KL explicitly.
- Kwan–Petrova–Sawhney, *Parities in random Latin squares*, arXiv:2509.13125;
  checked against the authors' PDF and publication listing. Row-by-row
  permanent comparison is established prior methodology. No novelty is claimed
  for completing an ordinary Latin rectangle through regular bipartite graphs.
- Kwan–Sah–Sawhney, *Large deviations in random Latin squares*,
  arXiv:2106.11932. Its intercalate statistics have repeated symbols and are
  distinguished from the strict distinct-rank order patterns in this paper.
- Gurvits, Electronic Journal of Combinatorics 15 (2008), R66,
  DOI 10.37236/790, arXiv:0711.3496. Publisher metadata and the primary paper
  support the permanent input. The capped upper-bound principle is described
  as Brègman-type; historical priority for it is not asserted.
- Traverso Gianini, CDR Papers I and III, DOIs 10.5281/zenodo.23987251 and
  10.5281/zenodo.24201563. Titles, theorem scope and release protocol were
  checked in `jtraverso/cdr-steiner-preprints` at the pinned commit. The actual
  finite Wilson source cut and its exact-type definitions are separately
  pinned in `lean/evidence/series_cdr_provenance.json`.

## Additional search

Queries included “Latinon large deviation principle”, “Latinons entropy
counting 2026” and the cited authors' primary material. The EuroComb extended
abstract on the authors' site also proposes entropy-based Latinon counting;
it is not used for the final normalization constant. No earlier full-space
Latinon LDP proof was identified in the primary material reviewed. This last
sentence is a report of the search, not a universal priority certification.

The manuscript's contribution is presented through its actual statements and
the profile correction/process proof. Requests for external review should
include an independent assessment of overlap with more recent counting work.

## Stable links

- https://arxiv.org/abs/2010.07854
- https://doi.org/10.19086/da.83253
- https://mkwn.github.io/PRLS.pdf
- https://arxiv.org/abs/2509.13125
- https://arxiv.org/abs/2106.11932
- https://www.combinatorics.org/ojs/index.php/eljc/article/view/v15i1r66
- https://doi.org/10.37236/790
- https://github.com/jtraverso/cdr-steiner-preprints

## Expanded gate requested by the author: alphaXiv and recent work

Checked on 15 November 2026. alphaXiv was used for discovery, followed by
the primary papers for theorem comparisons. The accessible alphaXiv entries
for Allsop--Morris and Divoux--Kelly--Kennedy--Sidhu displayed abstracts and
metadata; both explicitly had no generated overview. No generated overview,
audio summary, mirror, or search-result absence is treated as proof evidence.
Direct alphaXiv opens for 2010.07854, 2106.11932 and 2509.13125 failed in the
browser tool. Those unsuccessful opens are not counted as source reviews.

### Scope comparison

| Primary source and passage actually examined | Comparison with this candidate | Decision |
| --- | --- | --- |
| Allsop--Morris, *Universal probability bounds for partial Latin squares*, arXiv:2606.18174v2, Theorem 1.1 and Remark 1.2. Primary: https://arxiv.org/html/2606.18174v2 . Discovery: https://www.alphaxiv.org/abs/2606.18174 . | For a prescribed partial square with k entries using at most alpha n rows and beta n columns, 2 alpha + beta < 1, containment probabilities lie between (delta/n)^k and (Delta/n)^k, for fixed positive constants. Taking logarithms leaves an uncertainty proportional to k. At k of order n squared this is of the same order as the entropy-rate term we must identify. Its stated bound therefore does not directly supply the full ordered Latinon LDP or its rate. | Relevant adjacent work; distinguish exact cell containment from macroscopic profile neighborhoods. Do not claim that our LDP improves its local containment estimates. |
| Divoux--Kelly--Kennedy--Sidhu, *Subsquares in random Latin squares and rectangles*, arXiv:2311.04152v2, Theorem 1.6, Lemma 3.1 and the discussion after Section 3. Primary: https://arxiv.org/html/2311.04152v2 . Discovery: https://www.alphaxiv.org/abs/2311.04152 . | Their near-independent containment estimate concerns a sparse partial rectangle inside a uniform k by n rectangle with k < (1/2-alpha)n. Their proof uses switchings and robust expansion. They explicitly explain the obstruction to that approach beyond n/2 rows. Our statement concerns complete squares, prescribed bounded profiles and then the full limit space. | Acknowledge neighboring rectangle methods in the review dossier. Ordinary rectangle completion and short switching arguments are not standalone novelty claims. |
| Kwan--Pham, *Nonlinear lower-tail large deviations at criticality*, arXiv:2610.10233v2, Section 1.3, Theorems 1.17 and 1.20. https://arxiv.org/html/2610.10233v2 . | These give sharp second-order counts for anti-Pasch STS and Latin squares without intercalates. They concern repeated-symbol configurations, unlike our strict distinct-rank order patterns. Our CDR corollary preserves types and a fixed residue; it does not prescribe all Pasch counts or assert global avoidance. | Do not add an anti-Pasch or intercalate-avoidance claim to this paper. Such an extension needs a separate theorem and an updated priority comparison. |
| Borga--Feray--Winkler, *Permutons*, arXiv:2611.12104v1, Theorem 4.1 and Section 8.2, especially the Latinon paragraph. https://arxiv.org/html/2611.12104v1 . | The stated permuton LDP has speed n and concerns permutations. The Latinon paragraph recalls the GHHS limit theory, compactness, approximation and quasirandomness; it does not state a Latinon counting LDP. This is useful recent context, not a proof that no other Latinon result exists. | Distinguish the n-speed permutation analogy from the n-squared-speed Latin square theorem. |
| Kwok--Lau--Ramachandran, *Spectral analysis of matrix scaling and operator scaling*, SIAM J. Comput. 50 (2021), 1034--1102; primary abstract and authors' paper. https://arxiv.org/abs/1904.03213 ; https://cs.uwaterloo.ca/~lapchi/papers/spectral-scaling.pdf . | Spectral scaling, convergence, condition bounds and expander-supported matrices are established topics. Our deterministic proof uses a boxed transportation minimizer and a residual-diameter argument. A different proof method alone is not a standalone novelty certificate. | No general priority claim for stable matrix correction or scaling. Ask a specialist to compare the precise support, box and L1-defect contract. |
| Kun He, *Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling*, arXiv:2611.08963v1, Section 1.1, Theorems 1.1, 1.4--1.5 and technique overview. https://arxiv.org/html/2611.08963v1 . | The main iteration guarantee uses a finite diagonal scaling, its logarithmic scaling radius and endpoint spectral gap. Spectral certificates can give logarithmic radius and polynomial entrywise distortion. These examined statements do not directly give our constant-box additive correction with cost at most three times the total margin defect. No equivalence or impossibility of a reduction is claimed. | Recent adjacent work strengthens the reason to avoid advertising the correction lemma as a separate new scaling theory. It does not, from the examined statements, replace the Latinon process proof. |

The date displayed inside the Allsop--Morris HTML body differs from the arXiv
submission/revision metadata. The record above identifies the arXiv version
explicitly and makes no priority inference from that internal date. The
Permutons abstract page also has an inconsistent generated author-count
sentence; the named author list and primary HTML supply the attribution.

### Search log and limitations

The expanded query families were:

- `site:alphaxiv.org "Latinon" "entropy"`, `site:alphaxiv.org "Latinons"`,
  `site:alphaxiv.org "Latinon" counting`;
- `site:alphaxiv.org "Latin squares" "large deviations"`,
  `site:alphaxiv.org "Latin squares" counting`,
  `site:alphaxiv.org "Latin" entropy`;
- `"Latinon" "large deviation principle"`,
  `"Latinons" counting entropy conjecture`,
  `"Latinon" "entropy"`, `"Latinons" "large deviations"`,
  `Latinon entropy counting large deviation 2026 theorem`;
- `matrix scaling stability quasirandom support bounded entries l1 correction Hoffman`,
  `"Matrix Scaling and Spectral Gaps" Kwok Lau Ramachandran`,
  `"Spectral analysis of matrix scaling and operator scaling" arxiv`.

Searches also surfaced classical finite enumeration and discrepancy papers.
Their discovery abstracts were inspected for triage only; they were not
promoted to a full theorem-level comparison or used to certify priority.
Search indexing, inaccessible pages, alternate terminology, unpublished work
and very recent revisions remain limitations. The primary sources in the
comparison table are linked at the specific versions inspected.

### Gate decision and effect on the manuscript

PASS here means that the stated contribution survives this scoped comparison
and that the dossier records the important adjacent results and limits. No
earlier proof of the same full ordered Latinon LDP was identified in the
sources examined. This is not an exhaustive novelty or priority certificate.
Independent external review should explicitly address that question.

No theorem, constant, protected contract, or mathematical source was changed
by this expansion. The rendered candidate already separates distinct-rank
patterns from intercalates, labels the bipartite factorization application as
an exact reformulation, and restricts the CDR result to a fixed-residue family.
The new detailed comparisons are retained in this review dossier; no claim
about arbitrary typed STS, anti-Pasch completions or a new general theory of
matrix scaling is added to the manuscript.

## Literal source/model and proof-method check for candidate 0.5

The GHHS primary text was now compared literally at Definitions 3.5, 3.7,
3.16, 4.1--4.3, Sections 3.2.2--3.2.3 and Theorems 3.13, 4.7 and 12.2.
Definition 3.16 is the measure representation used here; the distance uses
the same pair of independent alignments and symbol-interval tests.
Proposition 2.3 prints the change-of-variables comparison. Compactness is
used as the published theorem with the identification made explicit.
The already-known law of large numbers is now attributed to Theorem 12.2.

Primary source: https://arxiv.org/html/2010.07854v3 . Its Section 12.2 prints
an entropy integral with positive sign. This manuscript explicitly uses
negative KL; no literal equality of those opposite sign conventions is
asserted. The source/model identification does not alter the metric.

Radhakrishnan's original article metadata was checked at the publisher:
JCTA 77 (1997), 161--164, https://doi.org/10.1006/jcta.1996.2727 . The original
full PDF was not retrieved. The entropy proof was read in the primary
Linial--Luria paper, Section 2, which reproduces it:
https://arxiv.org/html/1106.0649 . Its higher-dimensional revealing argument
is the antecedent for the two-owner bound. The publisher confirms Combinatorica
34 (2014), 471--486, https://doi.org/10.1007/s00493-011-2842-8 . The page range
80--83 in that paper's Radhakrishnan bibliography is not copied; the publisher
gives 161--164 for Radhakrishnan.

Kenyon--Král'--Radin--Winkler, *Permutations with fixed pattern densities*,
Theorem 1 and its introduction were read in the primary text:
https://arxiv.org/html/1506.02340 . They formulate the entropy LDP at speed n
and attribute its origin to Trashorras. Publisher metadata identifies Random
Structures & Algorithms 56 (2020), 220--250, with online publication in 2019:
https://doi.org/10.1002/rsa.20882 . This is cited directly in the manuscript.
It supplies context, not the n-squared-speed Latinon result.


Final pre-release positioning check, 16 November 2026: GHHS arXiv v3,
Remark 3.2, Definitions 3.3/3.7 and Conjecture 12.4 were read literally.
The finite normalization agrees exactly; the embedding error is separate.
The v2 locator 12.5 is from the author's supplied independent PDF review.
The Discrete Analysis landing page https://discreteanalysisjournal.com/article/83253-limits-of-latin-squares
links to arXiv for the article. No independent journal-PDF numbering check is
claimed. GHHS uses the positive displayed integral in Section 12.2; the
manuscript's confirmation uses negative KL and treats the extended cases
explicitly. This identifies the intended counting statement, not its literal
opposite-sign display. No unreleased colour-statistics work is cited.
