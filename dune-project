(lang dune 3.20)

(name sim)

(using dune_site 0.1)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name sim)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml)
 (allow_empty)
 (tags
  ("add topics" "to describe" your project)))

(package
 (name convlir)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml)
 (tags
  ("add topics" "to describe" your project)))

(package
 (name ppllvm)
 (synopsis "A BAP plugin for dumping symbol information")
 (allow_empty)
 (tags (bap bap-plugin))
 (depends
  (bap-std (= :version))
  (core_kernel (and (>= v0.14) (< v0.16)))
  (graphlib (= :version))
  (bap-common (= :version))
  (ppx_bap (= :version))
  (regular (= :version))))


; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
