# Series catalogue and publication policy

The repository collects preprints on combinatorial entropy and counting. Each
article is mathematically independent unless its own references explicitly
state a dependence. A series sequence number is catalogue metadata; it does
not change an article's title or theorem numbering.

| Sequence | Paper ID | Article | Edition | Package |
|---|---|---|---|---|
| Paper I | LATINON | Entropy and large deviations for Latin squares | 1.0 | [Paper directory](preprints/LATINON/README.md) |
| Research note | GHHSBRIDGE | The kernel and measure representations of Latinons agree: a Lean formalization | 1.0 | [Paper directory](preprints/GHHSBRIDGE/README.md) |
| Paper II | COLORSTATS | Counting Steiner triple systems and Latin squares with prescribed color statistics | 1.0 | [Paper directory](preprints/COLORSTATS/README.md) |
| Paper III | STEINER-PROFILES | Counting Steiner designs with prescribed color profiles | 1.0 | [Paper directory](preprints/STEINER-PROFILES/README.md) |

Only completed editions appear in this catalogue. No prospective article,
unreleased draft or forward mathematical dependency is listed.

Each paper uses `preprints/<PAPER_ID>/` with the five CDR-style subdirectories
for manuscript, validation, reproducibility, integrity and formalization.
Its release tag is `<paper-id>-v<version>`, independent of other papers.
The initial paper uses `latinon-v1.0`, the research note `ghhsbridge-v1.0` and Paper II `colorstats-v1.0`.
Later papers receive their own stable identifiers and tags; publishing one never
replaces another paper's freeze.

`PUBLICATION_INDEX.json` is the machine-readable catalogue. Root metadata and
navigation describe the collection; the paper directory carries the paper's
title, citations, version and evidence. Per-paper audits use identified names
in `publication/`, following the CDR series convention. Archives and checksum
sidecars are named per paper. Verifiers and CI record which paper they cover.

The research note GHHSBRIDGE depends on LATINON, as its references state: it
gives the Lean proof of Proposition 2.3 of the Latinon preprint and derives
Conjecture 12.4 of Garbe, Hancock, Hladký and Sharifzadeh in their own terms.
It adds files and catalogue entries; it changes no file of the Latinon paper.
The tag `latinon-v1.0` keeps the Latinon edition exactly as released.

Paper II, COLORSTATS, cites the Latinon paper and the research note and places
itself after them: Paper I counts Latin squares near a limit object, Paper II
counts designs with exactly prescribed color statistics. The research note sits
between the two papers and is not numbered as a paper. Paper II adds files and
catalogue entries; it changes no file of the Latinon paper or of the note. Its
Lean archive depends on the Lean sources of the CDR III preprint and on pinned
Mathlib, which are not bundled.

Repository visibility is an access setting,
separate from the edition bytes and its internal audit. Each public edition carries its own
source archive, verification evidence and citation. The Latinon DOI https://doi.org/10.5281/zenodo.24284129 and the GHHSBRIDGE DOI
https://doi.org/10.5281/zenodo.24293531 are reserved for their unpublished deposits, as is the COLORSTATS DOI https://doi.org/10.5281/zenodo.24308221. No journal acceptance is claimed.
