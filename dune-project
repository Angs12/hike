(lang dune 3.23)

(name hike)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name hike)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml)
 (tags
  ("add topics" "to describe" your project)))

; The vsa-debug profile — the sanctioned home for debug instrumentation
; (AGENTS.md principle 6): the vsa_debug/wbig_diag fixture probes build
; ONLY here (enabled_if), every other profile builds the production tree.
; Restored 2026-08-31 (the AGENTS.md doc-bug note: it was missing).
(profile
  (name vsa-debug)
  (env
    (ocamlopt_flags (:standard -O3))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
