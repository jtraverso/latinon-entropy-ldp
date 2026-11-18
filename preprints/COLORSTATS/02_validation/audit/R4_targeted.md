# Audit round 4 — targeted (independent agent, read-only, 17 Nov 2026)

Scope: `R4_BRIEF.md` — the author's second editorial round (abstract, §1.1 index, sentence after Corollary 1.11, opening of §6,
deductive openers), Lemmas 5.17 and 5.20 ("integer combination"), the new §1.7 and the formal companion, the Spanish passages, and
a regression sweep. Method: diff of the current EN/ES manuscripts against the version that passed round 3.

Verdict of the round: **NOT PASS** — three MENOR findings, no SERIO or BLOQUEANTE; all closed by the replacements below
(applied by `editorial/fix_round4.py`), and the closure was then checked (`R4_closure.md`).

| Item | Status |
|---|---|
| Abstract | OK (matches 1.1, 1.2, 1.5–1.8, Proposition 1.3, Corollary 1.4; P₀ and P as in §1.3; "Unlike earlier…" consistent with §1.4) |
| §1.1 index | OK |
| After Corollary 1.11 | F2 (MENOR) |
| Opening of §6 | OK (transversal triples §6.1; vertex balance §6.5, Lemma 6.3; intercalate exchanges Lemma 6.6) |
| "So" replacements | OK (14 places read in context; no dependency changed) |
| §1.7 and companion | F1 (MENOR) in §1.7; F3 (MENOR) in the companion; the rest supported |
| Regression sweep | OK (no dangling cross-reference; citations [1]–[36] in order; PARITY hashes current; TeX/PDF contain the changes) |
| Lemmas 5.17, 5.20 | OK; hypotheses equal to `E2Lattice.Rich`, `E3Lattice.Rich`; conclusion ℤ-span |
| Spanish passages | OK (same content as English) |

## Findings
- **F1 MENOR §1.7.** (a) The error O(n^{7/4}) is false for Theorem 1.9(a), which also loses O(ηn²) from typicality
  (`TypedGFinal.lean:140`); (b) the normalized forms with D(Q‖P) of Theorems 1.5 and 1.7 are not formalized; (c) "the upper bounds
  and the finite algebra of the paper" overstates the scope (Lemmas 4.1–4.2, 5.2, 5.7, 5.9, 6.1, 6.3, 6.5, 6.6 not formalized; the
  list of non-formalized results omitted Corollaries 1.4 and 1.11). Replacement applied in EN and ES.
- **F2 MENOR after Corollary 1.11.** [8, Theorem 1.1] completes sparse partial systems of allowed (bicolored) blocks to
  bicolored systems; Corollary 1.11 requires every block type, including monochromatic and rainbow ones, to have order n², so it does
  not count those completions. Replacement applied in EN and ES ("a counting counterpart … so it does not count the bicolored
  completions of [8, Theorem 1.1]").
- **F3 MENOR formal companion.** Three passages still said the paper writes "integer sum". Replaced in EN and ES.

## Editorial (applied)
E1 mapping-notes item 12 marked resolved; E2 companion: "(plus ηn² for Theorem 1.9(a))"; E3 Spanish "compleciones";
E4 abstract: "feasible counts" and "independent random coloring with the class proportions".

## Supported claims of §1.7 (verified)
89 queries with exactly [propext, Classical.choice, Quot.sound] in both axiom logs; no sorry/admit/axiom in the sources; (1.1) with
K = 8c (`LatinUpper.lean:569`); Proposition 1.3 with explicit error (`Prop13Bridge.lean:130`); Lemmas 5.12–5.14, 5.16–5.20 with
minor differences of form; dependence on the sources of [8] (corpus DOI equals [8]; imports `CountingCone.LL.*`,
`RequestProject.TypedTriangle.*`); T, T⁺ in [17] and [18] in [19] as in §1.4; [29] not formalized; O(n^{7/4}) correct for STS and
1-factorizations (`TypedFinal.lean:137`, `Typed1FMain.lean:160`).

## Coverage
VERIFIED: zip and 65 entry hashes against FREEZE; 5 log hashes; build logs (9030 jobs; 57 modules rebuilt from the archive); 89
axiom queries; all 89 declaration (module:line) references of the companion by script; 12 companion rows checked semantically against
the Lean source; the full EN/ES diff against round 3; cross-references and citation order; [8, Theorem 1.1] in its published text.
READ: proofs of §§5.8–5.10 and 6 around the changes; Appendices A–B; MAPPING_NOTES.md; DEPENDENCIES.md. No build was run.
Black boxes: T, T⁺, [17], [18], [19], [29], the corpus of [8] beyond hashes.
