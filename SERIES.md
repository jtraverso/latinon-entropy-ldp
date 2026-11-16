# Series catalogue and publication policy

The repository collects preprints on combinatorial entropy and counting. Each
article is mathematically independent unless its own references explicitly
state a dependence. A series sequence number is catalogue metadata; it does
not change an article's title or theorem numbering.

| Sequence | Paper ID | Article | Edition | Package |
|---|---|---|---|---|
| 1 | LATINON | Entropy and large deviations for Latin squares | 1.0 | [Paper directory](preprints/LATINON/README.md) |
| 2 | GHHSBRIDGE | The kernel and measure representations of Latinons agree: a Lean formalization (research note) | 1.0 | [Paper directory](preprints/GHHSBRIDGE/README.md) |

Only completed editions appear in this catalogue. No prospective article,
unreleased draft or forward mathematical dependency is listed.

Each paper uses `preprints/<PAPER_ID>/` with the five CDR-style subdirectories
for manuscript, validation, reproducibility, integrity and formalization.
Its release tag is `<paper-id>-v<version>`, independent of other papers.
The initial paper uses `latinon-v1.0` and the research note `ghhsbridge-v1.0`.
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

Repository visibility is an access setting,
separate from the edition bytes and its internal audit. Each public edition carries its own
source archive, verification evidence and citation. The Latinon DOI https://doi.org/10.5281/zenodo.24284129 and the GHHSBRIDGE DOI
https://doi.org/10.5281/zenodo.24293531 are reserved for their unpublished deposits. No journal acceptance is claimed.
